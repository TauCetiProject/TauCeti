/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.GroupTheory.GroupAction.Transitive
public import TauCeti.RepresentationTheory.Induction.Clifford.Multiplicity
public import TauCeti.RepresentationTheory.Induction.Clifford.Orbit.Basic
public import TauCeti.RepresentationTheory.Induction.Inertia
public import TauCeti.RingTheory.Semisimple.RegularIsotypicComponent

/-!
# Inertia cosets index the constituents in Clifford's theorem

This file identifies the orbit of an irreducible constituent in Clifford's theorem with the left
cosets of its inertia group. Concretely, if `σ` is a minimal subrepresentation of the restriction
of an irreducible finite-dimensional representation `ρ` from `G` to a normal subgroup `N`, then
the isotypic components of the restriction are indexed by

`G ⧸ inertia (FDRep.of σ.toRepresentation)`.

Translation by `ρ g` acts on the `k[N]`-submodules of the restriction
(`Representation.conjSubmoduleHom`) and carries the isotypic component of a constituent `τ` onto
that of its translate (`Representation.conjSubmoduleHom_isotypicComponent`), so `G` acts on the
isotypic components (`Representation.isotypicComponentsMulAction`). By the single-orbit theorem
of `TauCeti/RepresentationTheory/Induction/Clifford/Orbit/Basic.lean` the action is transitive
(`Representation.isPretransitive_isotypicComponents`), and the stabilizer of the component of `σ`
is the inertia group of `σ` (`Representation.stabilizer_conjSubrepIsotypicComponent_one`). The
indexing is then the orbit--stabilizer bijection `TauCeti.quotientStabilizerEquiv`,
and it is `G`-equivariant (`Representation.isotypicComponentsEquivQuotientInertia_smul`).

This is the orbit-indexing step of Clifford's theorem. The decomposition of the restriction as
equal-multiplicity copies of the conjugates indexed by these cosets is `FDRep.clifford_restrict_iso`
in `TauCeti/RepresentationTheory/Induction/Clifford/Equivalence.lean`.

## Main definitions

* `Representation.fdRepIsoConjSubrep`: the finite-dimensional representation carried by a
  translated constituent is isomorphic to the conjugate representation.
* `Representation.conjSubmoduleHom`: translation of `k[N]`-submodules of the restriction, as an
  action of `G` by order automorphisms.
* `Representation.isotypicComponentsMulAction`: the action of `G` on the isotypic components.
* `Representation.isotypicComponentsEquivQuotientInertia`: the equivalence between the isotypic
  components of the restriction and the inertia cosets.

The indexed component `Representation.conjSubrepIsotypicComponent` is defined in `Orbit/Basic.lean`.

## Main results

* `Representation.toSkeleton_fdRepOf_conjSubrep`: translating a constituent inside `ρ` and
  conjugating the abstract `N`-representation it carries agree on isomorphism classes.
* `Representation.mem_inertia_fdRepOf_toRepresentation_iff`: a group element lies in the inertia
  group of a constituent exactly when its translate carries an equivalent `k[N]`-submodule.
* `Representation.nonempty_linearEquiv_conjSubrep_iff`: translating two constituents by the same
  `g` preserves whether they are isomorphic, in any dimension.
* `Representation.conjSubmoduleHom_isotypicComponent`: translation carries the isotypic component
  of a constituent onto that of its translate.
* `Representation.isPretransitive_isotypicComponents` and
  `Representation.stabilizer_conjSubrepIsotypicComponent_one`: the action on components is
  transitive, with the inertia group of a constituent as stabilizer of its component.
* `Representation.isotypicComponentsEquivQuotientInertia_smul`: the indexing is `G`-equivariant.
* `Representation.isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent`: under the
  equivalence, the component of the translate by `g` corresponds to the coset of `g`.
* `Representation.isotypicComponentsEquivQuotientInertia_symm_mk`: the inverse computation.
* `Representation.conjSubrepIsotypicComponent_eq_iff`: two translates determine the same component
  exactly when their quotient lies in the inertia group.
* `Representation.card_isotypicComponents_eq_inertia_index`: the number of irreducible constituent
  classes is the index of the inertia group.

## Implementation notes

Equality of the isotypic components of two simple submodules is read through
`TauCeti.simpleSubmoduleClassesEquiv`. Isomorphism of subrepresentations is expressed as a
`k[N]`-linear equivalence of their associated submodules; the general bridge to equality in
`Skeleton (FDRep k N)` is `TauCeti.toSkeleton_fdRepOf_toRepresentation_eq_iff`.

## References

The mathematics is the classical orbit-stabilizer argument in C. W. Curtis and I. Reiner,
*Representation Theory of Finite Groups and Associative Algebras*, §49.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

universe u v

namespace Representation

open TauCeti

section OrbitIndex

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {V : Type u} [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)

/-- **A translated constituent carries the conjugate finite-dimensional representation.** -/
noncomputable def fdRepIsoConjSubrep [FiniteDimensional k V]
    (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    FDRep.of (conjSubrep ρ g σ).toRepresentation ≅
      conjNormalFDRep g (FDRep.of σ.toRepresentation) :=
  fdRepIsoOfAsModuleLinearEquiv
    (TauCeti.Representation.asModuleLinearEquivOfEquiv (conjSubrepEquiv ρ g σ).symm)

/-- Translating a constituent inside the ambient representation agrees, on isomorphism classes,
with conjugating the finite-dimensional representation carried by that constituent. -/
theorem toSkeleton_fdRepOf_conjSubrep [FiniteDimensional k V]
    (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    toSkeleton (FDRep.of (conjSubrep ρ g σ).toRepresentation) =
      g • toSkeleton (FDRep.of σ.toRepresentation) := by
  rw [smul_toSkeleton]
  exact toSkeleton_eq_toSkeleton_iff.mpr ⟨fdRepIsoConjSubrep ρ g σ⟩

/-- Membership in a constituent's inertia group is equivalence of the translated and original
associated submodules. -/
theorem mem_inertia_fdRepOf_toRepresentation_iff [FiniteDimensional k V]
    (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    g ∈ inertia (FDRep.of σ.toRepresentation) ↔
      Nonempty ((conjSubrep ρ g σ).asSubmodule ≃ₗ[k[N]] σ.asSubmodule) := by
  rw [mem_inertia_iff]
  constructor
  · rintro ⟨i⟩
    apply (toSkeleton_fdRepOf_toRepresentation_eq_iff _ _).mp
    exact toSkeleton_eq_toSkeleton_iff.mpr ⟨fdRepIsoConjSubrep ρ g σ ≪≫ i⟩
  · intro h
    obtain ⟨i⟩ := toSkeleton_eq_toSkeleton_iff.mp
      ((toSkeleton_fdRepOf_toRepresentation_eq_iff _ _).mpr h)
    exact ⟨(fdRepIsoConjSubrep ρ g σ).symm ≪≫ i⟩

/-- **Translation of `k[N]`-submodules of the restriction**: `conjSubrepHom` read across
`Subrepresentation.subrepresentationSubmoduleOrderIso`. The value at `g` sends the submodule of an
`N`-subrepresentation `σ` to that of its translate `ρ g '' σ`. -/
noncomputable def conjSubmoduleHom :
    G →* (Submodule k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) ≃o
      Submodule k[N] (_root_.Representation.asModule (ρ.comp N.subtype))) where
  toFun g := Subrepresentation.subrepresentationSubmoduleOrderIso.symm.trans
    ((conjSubrepHom ρ g).trans Subrepresentation.subrepresentationSubmoduleOrderIso)
  map_one' := RelIso.ext fun S ↦ by simp
  map_mul' g h := RelIso.ext fun S ↦ by
    simp only [map_mul, RelIso.mul_apply, OrderIso.trans_apply, OrderIso.symm_apply_apply]

/-- Translating the submodule of an `N`-subrepresentation gives the submodule of its translate. -/
@[simp]
theorem conjSubmoduleHom_asSubmodule (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    conjSubmoduleHom ρ g σ.asSubmodule = (conjSubrep ρ g σ).asSubmodule := by
  have hσ : Subrepresentation.subrepresentationSubmoduleOrderIso.symm σ.asSubmodule = σ :=
    Subrepresentation.subrepresentationSubmoduleOrderIso.symm_apply_apply σ
  simp only [conjSubmoduleHom, MonoidHom.coe_mk, OneHom.coe_mk, OrderIso.trans_apply, hσ,
    conjSubrepHom_apply, Subrepresentation.subrepresentationSubmoduleOrderIso_apply]

/-- Translating back by `ρ g⁻¹` inverts translation by `ρ g` on `k[N]`-submodules. -/
@[simp]
theorem conjSubmoduleHom_symm (g : G) :
    (conjSubmoduleHom ρ (N := N) g).symm = conjSubmoduleHom ρ (N := N) g⁻¹ :=
  RelIso.ext fun S ↦ by
    rw [OrderIso.symm_apply_eq, ← RelIso.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      RelIso.one_apply]

/-- Translation by `ρ g`, transporting a `k[N]`-linear equivalence `σ ≃ τ` to one between the
translates. Each of `ρ g⁻¹` and `ρ g` is only semilinear over conjugation, and the two twists
cancel. -/
private noncomputable def conjSubrepLinearEquiv (g : G) {σ τ : Subrepresentation (ρ.comp N.subtype)}
    (e : σ.asSubmodule ≃ₗ[k[N]] τ.asSubmodule) :
    (conjSubrep ρ g σ).asSubmodule ≃ₗ[k[N]] (conjSubrep ρ g τ).asSubmodule where
  toFun x := conjSubrepMap ρ g (fun v hv ↦ mem_conjSubrep_iff.mpr (by rwa [ρ.inv_self_apply]))
    (e (conjSubrepMap ρ g⁻¹ (fun _ hv ↦ mem_conjSubrep_iff.mp hv) x))
  invFun y := conjSubrepMap ρ g (fun v hv ↦ mem_conjSubrep_iff.mpr (by rwa [ρ.inv_self_apply]))
    (e.symm (conjSubrepMap ρ g⁻¹ (fun _ hv ↦ mem_conjSubrep_iff.mp hv) y))
  map_add' x y := by simp
  map_smul' a x := by
    simp only [conjSubrepMap_smul, map_smul, RingHom.id_apply, ← AlgEquiv.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, AlgEquiv.one_apply]
  left_inv x := by simp
  right_inv y := by simp

/-- Translating two `N`-subrepresentations by the same `g` does not change whether they are
isomorphic as representations of `N`. -/
theorem nonempty_linearEquiv_conjSubrep_iff (g : G)
    (σ τ : Subrepresentation (ρ.comp N.subtype)) :
    Nonempty ((conjSubrep ρ g σ).asSubmodule ≃ₗ[k[N]] (conjSubrep ρ g τ).asSubmodule) ↔
      Nonempty (σ.asSubmodule ≃ₗ[k[N]] τ.asSubmodule) := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨e⟩ ↦ ⟨conjSubrepLinearEquiv ρ g e⟩⟩
  have hσ : conjSubrep ρ g⁻¹ (conjSubrep ρ g σ) = σ := by
    rw [conjSubrep_conjSubrep, inv_mul_cancel, conjSubrep_one]
  have hτ : conjSubrep ρ g⁻¹ (conjSubrep ρ g τ) = τ := by
    rw [conjSubrep_conjSubrep, inv_mul_cancel, conjSubrep_one]
  exact ⟨(LinearEquiv.ofEq _ _ (congrArg Subrepresentation.asSubmodule hσ)).symm.trans
    ((conjSubrepLinearEquiv ρ g⁻¹ e).trans
      (LinearEquiv.ofEq _ _ (congrArg Subrepresentation.asSubmodule hτ)))⟩

/-- **Translation carries isotypic components to isotypic components**: `ρ g` carries the isotypic
component of `σ` onto that of the translate `conjSubrep ρ g σ`. -/
theorem conjSubmoduleHom_isotypicComponent (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    conjSubmoduleHom ρ g
        (isotypicComponent k[N] (_root_.Representation.asModule (ρ.comp N.subtype))
          σ.asSubmodule) =
      isotypicComponent k[N] (_root_.Representation.asModule (ρ.comp N.subtype))
        (conjSubrep ρ g σ).asSubmodule := by
  rw [isotypicComponent, isotypicComponent, OrderIso.map_sSup_eq_sSup_symm_preimage]
  congr 1
  ext S
  obtain ⟨τ, rfl⟩ := Subrepresentation.subrepresentationSubmoduleOrderIso.surjective S
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, conjSubmoduleHom_symm,
    Subrepresentation.subrepresentationSubmoduleOrderIso_apply, conjSubmoduleHom_asSubmodule]
  rw [← nonempty_linearEquiv_conjSubrep_iff ρ g, conjSubrep_conjSubrep, mul_inv_cancel,
    conjSubrep_one]

/-- Translation sends isotypic components of the restriction to isotypic components. -/
theorem conjSubmoduleHom_mem_isotypicComponents (g : G)
    (c : isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype))) :
    conjSubmoduleHom ρ g c.val ∈
      isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) := by
  obtain ⟨_, S, hS, rfl⟩ := c
  obtain ⟨σ, rfl⟩ := Subrepresentation.subrepresentationSubmoduleOrderIso.surjective S
  have hσ := Subrepresentation.isSimpleModule_asSubmodule_iff.mp hS
  refine ⟨_, Subrepresentation.isSimpleModule_asSubmodule_iff.mpr
    (isAtom_conjSubrep_iff (g := g).mpr hσ), ?_⟩
  exact conjSubmoduleHom_isotypicComponent ρ g σ

/-- **`G` acts on the isotypic components of the restriction**, by `g · c = ρ(g)(c)`. -/
noncomputable instance isotypicComponentsMulAction :
    MulAction G (isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype))) where
  smul g c := ⟨conjSubmoduleHom ρ g c.val, conjSubmoduleHom_mem_isotypicComponents ρ g c⟩
  -- `Subtype.ext` reduces each law to the underlying submodules, where the action is
  -- `conjSubmoduleHom ρ g`, a monoid hom into the order automorphisms.
  one_smul c := Subtype.ext <| by
    change conjSubmoduleHom ρ 1 c.val = c.val
    rw [map_one, RelIso.one_apply]
  mul_smul g h c := Subtype.ext <| by
    change conjSubmoduleHom ρ (g * h) c.val = conjSubmoduleHom ρ g (conjSubmoduleHom ρ h c.val)
    rw [map_mul, RelIso.mul_apply]

/-- The component `g · c` is the translate of `c` by `ρ g`. -/
@[simp]
theorem coe_smul_isotypicComponents (g : G)
    (c : isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype))) :
    ((g • c : isotypicComponents k[N] _) :
      Submodule k[N] (_root_.Representation.asModule (ρ.comp N.subtype))) =
      conjSubmoduleHom ρ g c :=
  (rfl)

/-- Acting by `g` on the component of the translate by `h` gives the component of the translate
by `g * h`. -/
@[simp]
theorem smul_conjSubrepIsotypicComponent [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g h : G) :
    g • conjSubrepIsotypicComponent ρ σ hσ h = conjSubrepIsotypicComponent ρ σ hσ (g * h) :=
  Subtype.ext <| by
    rw [coe_smul_isotypicComponents, coe_conjSubrepIsotypicComponent,
      coe_conjSubrepIsotypicComponent, conjSubmoduleHom_isotypicComponent, conjSubrep_conjSubrep]

/-- The component of the translate by `g` is `g` acting on the component of `σ`. -/
theorem conjSubrepIsotypicComponent_eq_smul [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    conjSubrepIsotypicComponent ρ σ hσ g = g • conjSubrepIsotypicComponent ρ σ hσ 1 := by
  rw [smul_conjSubrepIsotypicComponent, mul_one]

/-- **`G` permutes the isotypic components transitively.** -/
theorem isPretransitive_isotypicComponents [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    MulAction.IsPretransitive G
      (isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype))) := by
  have hrange : ∀ c : isotypicComponents k[N] _,
      ∃ g, c = conjSubrepIsotypicComponent ρ σ hσ g := by
    rintro ⟨c, hc⟩
    rw [isotypicComponents_eq_range ρ hσ] at hc
    obtain ⟨g, rfl⟩ := hc
    exact ⟨g, Subtype.ext (coe_conjSubrepIsotypicComponent ρ σ hσ g).symm⟩
  refine ⟨fun c d ↦ ?_⟩
  obtain ⟨g, rfl⟩ := hrange c
  obtain ⟨h, rfl⟩ := hrange d
  exact ⟨h * g⁻¹, by rw [smul_conjSubrepIsotypicComponent, inv_mul_cancel_right]⟩

variable [FiniteDimensional k V]

/-- **The stabilizer of the component of a constituent is its inertia group.** -/
theorem stabilizer_conjSubrepIsotypicComponent_one [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    MulAction.stabilizer G (conjSubrepIsotypicComponent ρ σ hσ 1) =
      inertia (FDRep.of σ.toRepresentation) := by
  ext g
  have := Subrepresentation.isSimpleModule_asSubmodule_iff.mpr hσ
  have := Subrepresentation.isSimpleModule_asSubmodule_iff.mpr
    (isAtom_conjSubrep_iff (g := g).mpr hσ)
  rw [MulAction.mem_stabilizer_iff, smul_conjSubrepIsotypicComponent, mul_one, Subtype.ext_iff,
    coe_conjSubrepIsotypicComponent, coe_conjSubrepIsotypicComponent, conjSubrep_one,
    isotypicComponent_eq_isotypicComponent_iff, mem_inertia_fdRepOf_toRepresentation_iff]

/-- **The inertia cosets index the isotypic components in Clifford's theorem.** It is the
orbit--stabilizer bijection `TauCeti.quotientStabilizerEquiv` for the transitive action of `G` on
the components, at the component of `σ`, whose stabilizer is the inertia group of `σ`. -/
noncomputable def isotypicComponentsEquivQuotientInertia [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) ≃
      G ⧸ inertia (FDRep.of σ.toRepresentation) :=
  haveI := isPretransitive_isotypicComponents ρ hσ
  (TauCeti.quotientStabilizerEquiv G (conjSubrepIsotypicComponent ρ σ hσ 1)).symm.trans
    (Subgroup.quotientEquivOfEq (stabilizer_conjSubrepIsotypicComponent_one ρ σ hσ))

/-- The coset of `g` is sent back to the component cut out by the translate by `g`. -/
@[simp]
theorem isotypicComponentsEquivQuotientInertia_symm_mk [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    (isotypicComponentsEquivQuotientInertia ρ σ hσ).symm (QuotientGroup.mk g) =
      conjSubrepIsotypicComponent ρ σ hσ g := by
  have := isPretransitive_isotypicComponents ρ hσ
  rw [conjSubrepIsotypicComponent_eq_smul, ← TauCeti.quotientStabilizerEquiv_mk,
    isotypicComponentsEquivQuotientInertia, Equiv.symm_trans_apply, Equiv.symm_symm]
  congr 1

/-- Under the Clifford orbit equivalence, the component of the translate by `g` corresponds to
the coset of `g`. -/
@[simp]
theorem isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent
    [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    isotypicComponentsEquivQuotientInertia ρ σ hσ
        (conjSubrepIsotypicComponent ρ σ hσ g) =
      QuotientGroup.mk g :=
  ((Equiv.symm_apply_eq _).mp (isotypicComponentsEquivQuotientInertia_symm_mk ρ σ hσ g)).symm

/-- **The Clifford orbit equivalence is `G`-equivariant**, for left multiplication on the inertia
cosets. -/
theorem isotypicComponentsEquivQuotientInertia_smul [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G)
    (c : isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype))) :
    isotypicComponentsEquivQuotientInertia ρ σ hσ (g • c) =
      g • isotypicComponentsEquivQuotientInertia ρ σ hσ c := by
  obtain ⟨q, rfl⟩ := (isotypicComponentsEquivQuotientInertia ρ σ hσ).symm.surjective c
  induction q using QuotientGroup.induction_on with
  | H h =>
    rw [isotypicComponentsEquivQuotientInertia_symm_mk, smul_conjSubrepIsotypicComponent,
      isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent,
      isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent,
      MulAction.Quotient.smul_mk, smul_eq_mul]

/-- Two translates cut out the same isotypic component exactly when they determine the same
inertia coset. -/
@[simp]
theorem conjSubrepIsotypicComponent_eq_iff [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g h : G) :
    conjSubrepIsotypicComponent ρ σ hσ g = conjSubrepIsotypicComponent ρ σ hσ h ↔
      g⁻¹ * h ∈ inertia (FDRep.of σ.toRepresentation) := by
  constructor
  · intro e
    have he := congrArg (isotypicComponentsEquivQuotientInertia ρ σ hσ) e
    simpa only [isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent,
      QuotientGroup.eq] using he
  · intro e
    apply (isotypicComponentsEquivQuotientInertia ρ σ hσ).injective
    rw [isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent,
      isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent]
    exact QuotientGroup.eq.mpr e

/-- **The number of constituent classes is the inertia index.** This is the numerical
orbit--stabilizer statement underlying the number of summands in Clifford's decomposition. -/
theorem card_isotypicComponents_eq_inertia_index [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    Nat.card (isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) =
      (inertia (FDRep.of σ.toRepresentation) : Subgroup G).index := by
  exact Nat.card_congr (isotypicComponentsEquivQuotientInertia ρ σ hσ)

end OrbitIndex

end Representation
