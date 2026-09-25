/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Decomposition
import TauCeti.LinearAlgebra.Trace.Pi
import TauCeti.RepresentationTheory.OfModule
import TauCeti.RepresentationTheory.Simple.Basic

/-
Roadmap source: `TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`, Layer 5.
-/

/-!
# The representation decomposition in Clifford's theorem

Let `N` be a normal subgroup of a group `G`, and let `W` be an irreducible
finite-dimensional representation of `G` over a splitting field. The isotypic components of the
restriction of `W` to `N` are indexed by the inertia cosets of any one constituent `V`, and every
component is a power of its constituent with one common positive exponent `e`. Combining these
two statements gives the classical decomposition

`Res_N W ≅ ⨁ (g : G / inertia V), e · {}^g V`.

The quotient index is preferable to a chosen transversal: `Quotient.out g` supplies the conjugate
representative, while changing that representative changes the summand only up to isomorphism.

## Main definitions

* `FDRep.cliffordSum`: the finite sum of `e` copies of the conjugate of `V` attached to every
  inertia coset.
## Main properties

* `FDRep.finrank_cliffordSum` and `FDRep.character_cliffordSum`: its dimension and character.

## Main result

* `FDRep.clifford_restrict_iso_of_isAtom`: **Clifford's theorem for a specified constituent**.
* `FDRep.clifford_restrict_iso`: **Clifford's theorem, representation form**. It supplies a
  simple constituent, finiteness of its inertia quotient, a positive common multiplicity, and an
  isomorphism from the restriction to `cliffordSum`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §49.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

universe u v

namespace FDRep

open TauCeti

/-- The finite sum of `e` copies of every conjugate of `V` indexed by the left cosets of its
inertia group. A finite product of modules is their direct sum; `FDRep.ofShrink` only returns its
possibly larger carrier to the universe in which `FDRep k N` lives. -/
noncomputable def cliffordSum {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] (V : FDRep k N) [Finite (G ⧸ inertia V)]
    (e : ℕ) : FDRep k N :=
  FDRep.ofShrink <| Representation.ofModule' (k := k) (G := N)
    ((q : G ⧸ inertia V) → Fin e →
      _root_.Representation.asModule (conjNormalFDRep (Quotient.out q) V).ρ)

/-- The dimension of `V.cliffordSum e` is the number of inertia cosets times `e` times the
dimension of `V`. -/
@[simp]
theorem finrank_cliffordSum {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] (V : FDRep k N) [Finite (G ⧸ inertia V)] (e : ℕ) :
    Module.finrank k (V.cliffordSum e) =
      Nat.card (G ⧸ inertia V) * e * Module.finrank k V := by
  classical
  let _ : Fintype (G ⧸ inertia V) := Fintype.ofFinite _
  rw [cliffordSum, finrank_ofShrink, Module.finrank_pi_fintype]
  simp_rw [Module.finrank_pi_fintype,
    (_root_.Representation.asModuleEquiv _).finrank_eq]
  simp [Nat.card_eq_fintype_card, mul_assoc]

/-- The character of `V.cliffordSum e` is `e` times the sum of the characters of its conjugate
summands. -/
@[simp]
theorem character_cliffordSum {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] (V : FDRep k N) [Finite (G ⧸ inertia V)]
    (e : ℕ) (x : N) :
    (V.cliffordSum e).character x =
      (e : k) * ∑ᶠ q : G ⧸ inertia V,
        (conjNormalFDRep (Quotient.out q) V).character x := by
  let _ : Fintype (G ⧸ inertia V) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, cliffordSum, character_ofShrink, Finset.mul_sum]
  simp only [Representation.char_ofModule'_pi, Representation.char_ofModule'_asModule,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- `FDRep.character V` and `V.ρ.character` both unfold to the trace of `V.ρ x`.
  simp only [FDRep.character, _root_.Representation.character]

end FDRep

namespace TauCeti

/-- The module carried by an isotypic component is `e` copies of the translated constituent that
defines it, where `e` is the common Clifford multiplicity. -/
private noncomputable def componentLinearEquiv
    {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G]
    {X : Type u} [AddCommGroup X] [Module k X] {N : Subgroup G} [N.Normal]
    (ρ : Representation k G X) [FiniteDimensional k X] [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (e : ℕ)
    (hcommon : ∀ τ : Subrepresentation (ρ.comp N.subtype), IsAtom τ →
      Module.finrank k
        (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) = e)
    (q : G ⧸ inertia (FDRep.of σ.toRepresentation)) :
    ((ρ.isotypicComponentsEquivQuotientInertia σ hσ).symm q).1 ≃ₗ[k[N]]
      Fin e → _root_.Representation.asModule
        (conjNormalFDRep (Quotient.out q) (FDRep.of σ.toRepresentation)).ρ := by
  let g : G := Quotient.out q
  have hq : QuotientGroup.mk g = q := Quotient.out_eq' q
  have hc : (ρ.isotypicComponentsEquivQuotientInertia σ hσ).symm q =
      ρ.conjSubrepIsotypicComponent σ hσ g := by
    rw [← hq]
    exact ρ.isotypicComponentsEquivQuotientInertia_symm_mk σ hσ g
  let τ := Representation.conjSubrep ρ g σ
  have hτ : IsAtom τ := Representation.isAtom_conjSubrep_iff.mpr hσ
  let _ : IsSimpleModule k[N] τ.asSubmodule :=
    Subrepresentation.isSimpleModule_asSubmodule_iff.mpr hτ
  let _ : FiniteDimensional k τ.asSubmodule :=
    Module.Finite.of_injective (τ.asSubmodule.subtype.restrictScalars k) Subtype.val_injective
  let eComponent := (nonempty_linearEquiv_isotypicComponent
    (k := k) (A := k[N])
    (M := _root_.Representation.asModule (ρ.comp N.subtype)) (S := τ.asSubmodule)).some
  have hmultiplicity : Module.finrank k
      (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) = e :=
    hcommon τ hτ
  rw [hmultiplicity] at eComponent
  let i := Representation.fdRepIsoConjSubrep ρ g σ
  let iRep := (nonempty_fdRepIso_iff.mp ⟨i⟩).some
  let eConj : τ.asSubmodule ≃ₗ[k[N]] _root_.Representation.asModule
      (conjNormalFDRep g (FDRep.of σ.toRepresentation)).ρ :=
    (_root_.Subrepresentation.asModuleEquivAsSubmodule τ).symm.trans
      (Representation.asModuleLinearEquivOfEquiv iRep)
  rw [hc, Representation.coe_conjSubrepIsotypicComponent]
  simpa only [τ, g] using
    eComponent.trans (LinearEquiv.piCongrRight fun _ ↦ eConj)

/-- The inertia group of a simple constituent of the restriction to `N` of a finite-dimensional
irreducible representation has finite index. -/
private theorem finite_quotient_inertia {k : Type u} {G : Type v} [Field k] [Group G] {X : Type u}
    [AddCommGroup X] [Module k X] {N : Subgroup G} [N.Normal] (ρ : Representation k G X)
    [FiniteDimensional k X] [ρ.IsIrreducible] (σ : Subrepresentation (ρ.comp N.subtype))
    (hσ : IsAtom σ) : Finite (G ⧸ inertia (FDRep.of σ.toRepresentation)) :=
  -- The restriction is a Noetherian `k[N]`-module, so it has finitely many isotypic components,
  -- and these are indexed by the inertia cosets.
  have : IsNoetherian k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) :=
    isNoetherian_of_tower k inferInstance
  .of_equiv _ (ρ.isotypicComponentsEquivQuotientInertia σ hσ)

/-- **Clifford's decomposition of the module of the restriction.**  The `k[N]`-module carried by
the restriction to `N` is the product, over the inertia cosets of a simple constituent `σ`, of `e`
copies of the translate of `σ`, where `e` is the common Clifford multiplicity. -/
private noncomputable def restrictLinearEquivPi {k : Type u} {G : Type v} [Field k] [IsAlgClosed k]
    [Group G] {X : Type u} [AddCommGroup X] [Module k X] {N : Subgroup G} [N.Normal]
    (ρ : Representation k G X) [FiniteDimensional k X] [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (e : ℕ)
    (hcommon : ∀ τ : Subrepresentation (ρ.comp N.subtype), IsAtom τ → Module.finrank k
      (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) = e) :
    _root_.Representation.asModule (ρ.comp N.subtype) ≃ₗ[k[N]]
      ((q : G ⧸ inertia (FDRep.of σ.toRepresentation)) → Fin e → _root_.Representation.asModule
        (conjNormalFDRep (Quotient.out q) (FDRep.of σ.toRepresentation)).ρ) :=
  let M := _root_.Representation.asModule (ρ.comp N.subtype)
  have : IsSemisimpleModule k[N] M :=
    (_root_.Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp
      (Representation.isSemisimpleRepresentation_comp_subtype ρ)
  have : IsNoetherian k[N] M := isNoetherian_of_tower k inferInstance
  let _ : Fintype (isotypicComponents k[N] M) := Fintype.ofFinite _
  -- `M` is the internal direct sum of its finitely many isotypic components, which
  -- `isotypicComponentsEquivQuotientInertia` indexes by the inertia cosets; each component is `e`
  -- copies of its translated constituent.
  (((sSupIndep_iff _).mp (sSupIndep_isotypicComponents k[N] M)).linearEquiv
    ((sSup_eq_iSup' _).symm.trans (sSup_isotypicComponents k[N] M))).symm ≪≫ₗ
    DFinsupp.linearEquivFunOnFintype ≪≫ₗ
    .piCongrLeft' k[N] (fun c ↦ c.1) (ρ.isotypicComponentsEquivQuotientInertia σ hσ) ≪≫ₗ
    .piCongrRight fun q ↦ componentLinearEquiv ρ σ hσ e hcommon q

end TauCeti

namespace FDRep

open TauCeti

/-- **Clifford's theorem for a specified constituent.** Given a simple constituent `σ` of the
restriction of an irreducible representation to a normal subgroup, the restriction is isomorphic
to `e` copies of every conjugate of `σ`, with the distinct conjugates indexed by the left cosets
of its inertia group.

Algebraic closure makes `k` a splitting field, so the Hom-space dimension in the multiplicity
theorem is the actual number of copies. Finite dimensionality makes the set of isotypic components,
and hence the inertia quotient indexing the sum, finite. -/
theorem clifford_restrict_iso_of_isAtom {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] [IsAlgClosed k]
    (W : FDRep k G) [Simple W] (σ : Subrepresentation (W.ρ.comp N.subtype))
    (hσ : IsAtom σ) :
    ∃ hfinite : Finite (G ⧸ inertia (FDRep.of σ.toRepresentation)),
      let _ := hfinite
      ∃ e : ℕ, e ≠ 0 ∧
        Nonempty (resFDRep N W ≅ (FDRep.of σ.toRepresentation).cliffordSum e) := by
  have : Representation.IsIrreducible W.ρ := FDRep.isIrreducible_of_simple W
  obtain ⟨e, he, hcommon⟩ := Representation.exists_forall_finrank_linearMap_eq (N := N) W.ρ
  have hfinite := finite_quotient_inertia W.ρ σ hσ
  refine ⟨hfinite, e, he.ne', nonempty_fdRepIso_iff.mpr ⟨?_⟩⟩
  -- The one definitional step: `resFDRep` is `Action.res` along `N.subtype`, which keeps the
  -- carrier (`Action.res_obj_V`) and precomposes the action (`Action.res_obj_ρ`).  The equation
  -- only typechecks up to that carrier identification, so it is recorded by `rfl`.
  have hres : (resFDRep N W).ρ = W.ρ.comp N.subtype := rfl
  rw [hres, cliffordSum]
  exact (Representation.equivOfAsModuleLinearEquiv (restrictLinearEquivPi W.ρ σ hσ e hcommon ≪≫ₗ
    (Representation.ofModule'AsModuleEquiv _).symm)).trans (FDRep.ofShrinkEquiv _).symm

/-- **Clifford's theorem, representation form.** The restriction of an irreducible
representation to a normal subgroup is isomorphic to `e` copies of every conjugate of one simple
constituent, with the distinct conjugates indexed by the left cosets of its inertia group.

Algebraic closure makes `k` a splitting field, so the Hom-space dimension in the multiplicity
theorem is the actual number of copies. The conclusion includes the finite inertia quotient that
indexes the sum. -/
theorem clifford_restrict_iso {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] [IsAlgClosed k]
    (W : FDRep k G) [Simple W] :
    ∃ (V : FDRep k N) (_ : Simple V) (hfinite : Finite (G ⧸ inertia V)),
      let _ := hfinite
      ∃ e : ℕ, e ≠ 0 ∧ Nonempty (resFDRep N W ≅ V.cliffordSum e) := by
  classical
  let _ : Representation.IsIrreducible W.ρ := FDRep.isIrreducible_of_simple W
  obtain ⟨σ, hσ, -⟩ :=
    Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep (N := N) W.ρ
  let V : FDRep k N := FDRep.of σ.toRepresentation
  let _ : Representation.IsIrreducible V.ρ :=
    Representation.isIrreducible_toRepresentation_of_isAtom hσ
  let _ : Simple V := FDRep.simple_of_isIrreducible V
  obtain ⟨hfinite, e, he, h⟩ := W.clifford_restrict_iso_of_isAtom σ hσ
  exact ⟨V, inferInstance, hfinite, e, he, h⟩

end FDRep
