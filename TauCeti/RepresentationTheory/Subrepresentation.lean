/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.RepresentationTheory.Intertwining

/-!
# The underlying module of a subrepresentation

Mathlib's `Subrepresentation` API records how `toSubmodule` interacts with the lattice
operations — `Subrepresentation.toSubmodule_sup` and `Subrepresentation.toSubmodule_inf`, both
`@[simp]` and both true by `rfl` — but not how it interacts with the bounded-lattice structure,
nor how it interacts with the order relations themselves, nor how it interacts with membership.
This file adds the six missing counterparts, in the same shape, together with the carriers of
`⊥` and `⊤` and membership in them. It also records that the
representation action on a subrepresentation is the restriction of the original action and
coerces to it, when an intertwining map is zero and when it is surjective in terms of the
subrepresentation its range is,
the inclusion of a subrepresentation as an intertwining map, that the group-algebra action on a
subrepresentation coerces to the original action, the canonical equivalence between the module of
the restricted representation and the corresponding submodule, that membership in a supremum of
subrepresentations is the same in the lattices of `A[G]`-submodules and of `A`-submodules, and
that a subrepresentation is minimal exactly when the `A[G]`-submodule it carries is simple.

They are stated at the typeclasses `Subrepresentation` itself asks for, so they apply wherever
the abstraction does. The `⊥` and `⊤` lemmas let proofs about extreme subrepresentations avoid
asserting the definitional unfolding of the `BoundedOrder` instance by hand; the `≤` and `<`
lemmas move an order statement between the two lattices, which is what lets a submodule-level
argument — a dimension count, say, or an orthogonal complement — settle a question about
subrepresentations; and the membership lemma does the same for a single element, so that a
carrier computed by a `toSubmodule` lemma answers a `SetLike` membership goal without unfolding
the `SetLike` instance by hand. `Subrepresentation.spanSingleton` packages the line through a
vector that every `ρ g` sends to a scalar multiple of itself, a common way to exhibit a proper
nonzero subrepresentation. `Representation.IntertwiningMap.eq_zero_iff_range_eq_bot` and
`Representation.IntertwiningMap.surjective_iff_range_eq_top` are the first consumers of the `⊥` and
`⊤` lemmas, and belong here because `⊥` and `⊤` of `Subrepresentation` have no other API: they are
`LinearMap.range_eq_bot` and `LinearMap.range_eq_top` moved up to the subrepresentation lattice,
and `Subrepresentation.subtype_eq_zero_iff` and `Subrepresentation.subtype_surjective_iff` below
are what they are proved for. In the same spirit,
`Subrepresentation.isSimpleModule_asSubmodule_iff` moves the notion of an irreducible constituent
across `Subrepresentation.subrepresentationSubmoduleOrderIso`, so that Mathlib's simple- and
semisimple-module API applies to minimal subrepresentations; being about `asSubmodule` it asks for
the coefficients to be a commutative ring, as `Subrepresentation.asSubmodule` and
`IsSimpleModule` between them do.  `Subrepresentation.isCompl_toSubmodule` is one more entry in
the lattice dictionary, moving `IsCompl` across it, and stated with the rest of that dictionary at
the typeclasses `Subrepresentation` itself asks for. The same dictionary shows that the
subrepresentations of a representation on a module over a ring form a modular lattice
(`Subrepresentation.instIsModularLattice`), as the submodules do.  Finally,
`Subrepresentation.equivProdOfIsCompl` upgrades a complement to an equivalence of representations
`ρ ≃ ρ₁ × ρ₂`: `Submodule.prodEquivOfIsCompl` supplies the linear isomorphism and each `ρ g`,
being additive and preserving both summands, supplies the equivariance.  Being about
`Submodule.prodEquivOfIsCompl`, it asks for the coefficients to be a ring and the module to be a
group, as that construction does.  Its first component is the projection
`Submodule.projectionOnto` along the complement, which therefore intertwines
(`Subrepresentation.isIntertwiningMap_projectionOnto`); its transpose, given by
`Representation.IsIntertwiningMap.dualMap`, extends linear forms on `ρ₁` by zero on `ρ₂`, which
includes the dual of `ρ₁` equivariantly into the dual of `ρ`. Annihilators exchange
subrepresentations of `ρ` and of its dual: `Subrepresentation.dualAnnihilator` and
`Subrepresentation.dualCoannihilator` carry `Submodule.dualAnnihilator` and
`Submodule.dualCoannihilator`.

The subrepresentations whose underlying submodule is finitely generated form a join-semilattice
(`Subrepresentation.instSemilatticeSupFG`), as the finitely generated submodules do in Mathlib, so
they can index a filtered colimit.

The subrepresentation `A[G] · v` generated by a vector is
`Representation.cyclicSubrepresentation ρ v`, the cyclic `A[G]`-submodule spanned by `v` read
through `Subrepresentation.ofSubmodule'`, so that its `A[G]`-submodule is that span
(`Representation.asSubmodule_cyclicSubrepresentation`). It is the least subrepresentation
containing `v` (`Representation.cyclicSubrepresentation_le_iff`), and its vectors are the
`A`-linear combinations of the translates `ρ g v`
(`Representation.toSubmodule_cyclicSubrepresentation`), whose span is invariant under `ρ`
(`Representation.apply_mem_span_range_apply`).

Restriction along any monoid homomorphism keeps the underlying submodule of a subrepresentation
(`Subrepresentation.res`), and the restricted subrepresentation carries the restricted
representation (`Subrepresentation.toRepresentation_res`). Restriction along a surjective monoid
homomorphism identifies the lattices of invariant submodules, keeping the underlying submodule in
both directions. In particular it preserves irreducibility, as does restriction along a monoid
isomorphism. Restriction of an algebra action along a monoid homomorphism whose image spans the
algebra keeps the invariant submodules too
(`AlgHom.mem_invtSubmodule_toMonoidHom_comp_iff_of_span_eq_top`).

## Main results

* `Subrepresentation.res`
* `Subrepresentation.toRepresentation_res`
* `MonoidHom.resSubrepresentationOrderIso`
* `MonoidHom.isIrreducible_comp_surjective_iff`
* `MulEquiv.isIrreducible_comp_equiv_iff`
* `AlgHom.mem_invtSubmodule_toMonoidHom_comp_iff_of_span_eq_top`
* `Representation.apply_mem_span_range_apply`
* `Representation.cyclicSubrepresentation`
* `Representation.asSubmodule_cyclicSubrepresentation`
* `Representation.mem_cyclicSubrepresentation_self`
* `Representation.cyclicSubrepresentation_le_iff`
* `Representation.toSubmodule_cyclicSubrepresentation`
* `Representation.mem_cyclicSubrepresentation_iff`
* `Subrepresentation.mem_toSubmodule`
* `Subrepresentation.toSubmodule_bot`
* `Subrepresentation.toSubmodule_top`
* `Subrepresentation.instNontrivial`
* `Subrepresentation.spanSingleton`
* `Subrepresentation.toSubmodule_spanSingleton`
* `Subrepresentation.mem_spanSingleton`
* `Subrepresentation.self_mem_spanSingleton`
* `Subrepresentation.toSubmodule_le_toSubmodule`
* `Subrepresentation.toSubmodule_lt_toSubmodule`
* `Subrepresentation.isCompl_toSubmodule`
* `Subrepresentation.instIsModularLattice`
* `Subrepresentation.toRepresentation_apply`
* `Subrepresentation.coe_toRepresentation_apply`
* `Subrepresentation.instIsTrivialToRepresentation`
* `Representation.IntertwiningMap.eq_zero_iff_range_eq_bot`
* `Representation.IntertwiningMap.surjective_iff_range_eq_top`
* `Subrepresentation.subtype`
* `Subrepresentation.coe_subtype`
* `Subrepresentation.toLinearMap_subtype`
* `Subrepresentation.subtype_injective`
* `Subrepresentation.range_subtype`
* `Subrepresentation.ker_subtype`
* `Subrepresentation.subtype_eq_zero_iff`
* `Subrepresentation.subtype_surjective_iff`
* `Subrepresentation.isIntertwiningMap_dualRestrict`
* `Subrepresentation.dualAnnihilator`
* `Subrepresentation.mem_dualAnnihilator`
* `Subrepresentation.dualCoannihilator`
* `Subrepresentation.mem_dualCoannihilator`
* `Subrepresentation.coe_toRepresentation_asAlgebraHom_apply`
* `Subrepresentation.asModuleEquivAsSubmodule`
* `Subrepresentation.intertwiningMapEquivLinearMapAsSubmodule`
* `Subrepresentation.mem_iSup_asSubmodule_iff`
* `Subrepresentation.isSimpleModule_asSubmodule_iff`
* `Subrepresentation.equivProdOfIsCompl`
* `Subrepresentation.isIntertwiningMap_projectionOnto`
* `Subrepresentation.instSemilatticeSupFG`
-/

public section

namespace Subrepresentation

variable {A G W : Type*} [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}

/-- A vector lies in the subspace a subrepresentation carries exactly when it lies in the
subrepresentation. This is the `SetLike` instance of `Subrepresentation`, whose coercion is
`toSubmodule`, stated as a lemma so that proofs need not unfold it. -/
@[simp]
lemma mem_toSubmodule {ρ' : Subrepresentation ρ} {v : W} : v ∈ ρ'.toSubmodule ↔ v ∈ ρ' := Iff.rfl

/-- The bottom subrepresentation carries the bottom subspace. -/
@[simp]
lemma toSubmodule_bot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

/-- The top subrepresentation carries the top subspace. -/
@[simp]
lemma toSubmodule_top : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

/-- The bottom subrepresentation consists of the zero vector. -/
@[simp, norm_cast]
lemma coe_bot : ((⊥ : Subrepresentation ρ) : Set W) = {0} := Submodule.bot_coe

/-- The top subrepresentation consists of every vector. -/
@[simp, norm_cast]
lemma coe_top : ((⊤ : Subrepresentation ρ) : Set W) = Set.univ := Submodule.top_coe

/-- A vector lies in the bottom subrepresentation exactly when it is zero. -/
@[simp, grind =]
lemma mem_bot {v : W} : v ∈ (⊥ : Subrepresentation ρ) ↔ v = 0 := Submodule.mem_bot A

/-- Every vector lies in the top subrepresentation. -/
@[simp]
lemma mem_top {v : W} : v ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top

/-- The subrepresentation lattice of a nontrivial representation is nontrivial. -/
instance instNontrivial [Nontrivial W] : Nontrivial (Subrepresentation ρ) :=
  ⟨⟨⊥, ⊤, fun hc => _root_.bot_ne_top (α := Submodule A W) (by
    rw [← toSubmodule_bot (ρ := ρ), ← toSubmodule_top (ρ := ρ), hc])⟩⟩

/-- **The line through a common eigenvector.** If every `ρ g` sends `v` to a scalar multiple of
`v`, then the span of `v` is a subrepresentation. -/
def spanSingleton (v : W) (h : ∀ g, ∃ t : A, ρ g v = t • v) : Subrepresentation ρ where
  toSubmodule := A ∙ v
  apply_mem_toSubmodule g x hx := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨t, ht⟩ := h g
    rw [map_smul, ht]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))

/-- The line through a common eigenvector carries the span of that vector. -/
@[simp]
lemma toSubmodule_spanSingleton (v : W) (h : ∀ g, ∃ t : A, ρ g v = t • v) :
    (spanSingleton v h).toSubmodule = A ∙ v :=
  (rfl)

/-- A vector lies in the line through a common eigenvector `v` exactly when it is a multiple
of `v`. -/
lemma mem_spanSingleton {v x : W} {h : ∀ g, ∃ t : A, ρ g v = t • v} :
    x ∈ spanSingleton v h ↔ ∃ a : A, a • v = x :=
  Submodule.mem_span_singleton

/-- A common eigenvector lies in the line it spans. -/
@[simp]
lemma self_mem_spanSingleton (v : W) (h : ∀ g, ∃ t : A, ρ g v = t • v) :
    v ∈ spanSingleton v h :=
  Submodule.mem_span_singleton_self v

/-- One subrepresentation is contained in another exactly when the subspace it carries is. -/
@[simp]
lemma toSubmodule_le_toSubmodule {ρ₁ ρ₂ : Subrepresentation ρ} :
    ρ₁.toSubmodule ≤ ρ₂.toSubmodule ↔ ρ₁ ≤ ρ₂ := Iff.rfl

/-- One subrepresentation is strictly contained in another exactly when the subspace it carries
is. -/
@[simp]
lemma toSubmodule_lt_toSubmodule {ρ₁ ρ₂ : Subrepresentation ρ} :
    ρ₁.toSubmodule < ρ₂.toSubmodule ↔ ρ₁ < ρ₂ := by
  simp only [lt_iff_le_not_ge, toSubmodule_le_toSubmodule]

/-- Two subrepresentations are complementary exactly when the subspaces they carry are.  This is
the counterpart, for `IsCompl`, of `Subrepresentation.toSubmodule_le_toSubmodule`: it is what lets
a splitting established in the submodule lattice -- by a dimension count, say, or by an explicit
projection -- be read as a splitting of representations. -/
@[simp]
theorem isCompl_toSubmodule {ρ₁ ρ₂ : Subrepresentation ρ} :
    IsCompl ρ₁.toSubmodule ρ₂.toSubmodule ↔ IsCompl ρ₁ ρ₂ := by
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← toSubmodule_inf, ← toSubmodule_sup,
    ← toSubmodule_bot (ρ := ρ), ← toSubmodule_top (ρ := ρ), toSubmodule_injective.eq_iff]

/-- The subrepresentations of a representation on a module over a ring form a modular lattice, as
the submodules they carry do. So Mathlib's modular-lattice API applies to them: in a semisimple
representation, for instance, a subrepresentation has a complement inside any larger one
(`IsModularLattice.exists_disjoint_and_sup_eq`). -/
instance instIsModularLattice {A W : Type*} [Ring A] [AddCommGroup W] [Module A W]
    {ρ : Representation A G W} : IsModularLattice (Subrepresentation ρ) :=
  ⟨fun {_} _ {_} h ↦ by
    rw [← toSubmodule_le_toSubmodule, toSubmodule_inf, toSubmodule_sup, toSubmodule_sup,
      toSubmodule_inf]
    exact IsModularLattice.sup_inf_le_assoc_of_le _ (toSubmodule_le_toSubmodule.2 h)⟩

/-- The action on a subrepresentation is the restriction of the original action. -/
theorem toRepresentation_apply (S : Subrepresentation ρ) (g : G) :
    S.toRepresentation g = (ρ g).restrict (S.apply_mem_toSubmodule g) :=
  rfl

/-- The action on a subrepresentation coerces to the original action. -/
@[simp]
theorem coe_toRepresentation_apply (S : Subrepresentation ρ) (g : G) (v : S.toSubmodule) :
    (S.toRepresentation g v : W) = ρ g v :=
  rfl

/-- A subrepresentation of a trivial representation is trivial. -/
instance instIsTrivialToRepresentation [ρ.IsTrivial] (S : Subrepresentation ρ) :
    S.toRepresentation.IsTrivial :=
  ⟨fun g ↦ LinearMap.ext fun v ↦ Subtype.ext <| by
    rw [coe_toRepresentation_apply, ρ.isTrivial_apply, LinearMap.id_apply]⟩

/-- An intertwining map is zero exactly when its range is the bottom subrepresentation. -/
theorem _root_.Representation.IntertwiningMap.eq_zero_iff_range_eq_bot
    {V : Type*} [AddCommMonoid V] [Module A V] {τ : Representation A G V}
    (f : Representation.IntertwiningMap ρ τ) : f = 0 ↔ f.range = ⊥ := by
  rw [← (Representation.IntertwiningMap.toLinearMap_injective ρ τ).eq_iff,
    Representation.IntertwiningMap.zero_toLinearMap, ← LinearMap.range_eq_bot,
    ← Subrepresentation.toSubmodule_injective.eq_iff,
    Representation.IntertwiningMap.range_toSubmodule, Subrepresentation.toSubmodule_bot]

/-- An intertwining map is surjective exactly when its range is the top subrepresentation. -/
theorem _root_.Representation.IntertwiningMap.surjective_iff_range_eq_top
    {V : Type*} [AddCommMonoid V] [Module A V] {τ : Representation A G V}
    (f : Representation.IntertwiningMap ρ τ) : Function.Surjective f ↔ f.range = ⊤ := by
  rw [← Representation.IntertwiningMap.coe_toLinearMap, ← LinearMap.range_eq_top,
    ← Subrepresentation.toSubmodule_injective.eq_iff,
    Representation.IntertwiningMap.range_toSubmodule, Subrepresentation.toSubmodule_top]

/-- **The inclusion of a subrepresentation**, as an intertwining map: the analogue of
`Submodule.subtype`, which is the linear map underlying it. -/
def subtype (ρ' : Subrepresentation ρ) :
    Representation.IntertwiningMap ρ'.toRepresentation ρ where
  toLinearMap := ρ'.toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

/-- The inclusion of a subrepresentation acts by the subtype coercion. -/
@[simp]
lemma coe_subtype (ρ' : Subrepresentation ρ) : ⇑ρ'.subtype = Subtype.val := by rfl

/-- The linear map underlying the inclusion is the submodule subtype map. -/
@[simp]
lemma toLinearMap_subtype (ρ' : Subrepresentation ρ) :
    ρ'.subtype.toLinearMap = ρ'.toSubmodule.subtype := by rfl

/-- The range of the inclusion of a subrepresentation is that subrepresentation. -/
@[simp]
theorem range_subtype (ρ' : Subrepresentation ρ) : ρ'.subtype.range = ρ' := by
  apply toSubmodule_injective
  rw [Representation.IntertwiningMap.range_toSubmodule, toLinearMap_subtype,
    Submodule.range_subtype]

/-- The kernel of the inclusion of a subrepresentation is zero. -/
@[simp]
theorem ker_subtype (ρ' : Subrepresentation ρ) : ρ'.subtype.ker = ⊥ := by
  apply toSubmodule_injective
  rw [Representation.IntertwiningMap.ker_toSubmodule, toLinearMap_subtype, Submodule.ker_subtype,
    toSubmodule_bot]

/-- The inclusion of a subrepresentation is injective. -/
theorem subtype_injective (ρ' : Subrepresentation ρ) : Function.Injective ρ'.subtype := by
  simpa only [coe_subtype] using Subtype.val_injective

/-- The inclusion of a subrepresentation is zero exactly when the subrepresentation is zero. -/
@[simp]
theorem subtype_eq_zero_iff (ρ' : Subrepresentation ρ) : ρ'.subtype = 0 ↔ ρ' = ⊥ := by
  rw [Representation.IntertwiningMap.eq_zero_iff_range_eq_bot, range_subtype]

/-- The inclusion of a subrepresentation is surjective exactly when the subrepresentation is the
whole representation. -/
theorem subtype_surjective_iff (ρ' : Subrepresentation ρ) :
    Function.Surjective ρ'.subtype ↔ ρ' = ⊤ := by
  rw [Representation.IntertwiningMap.surjective_iff_range_eq_top, range_subtype]

/-- Restricting linear forms to a subrepresentation intertwines the dual representation with the
dual of the subrepresentation: it is the transpose of the inclusion. -/
theorem isIntertwiningMap_dualRestrict {k H V : Type*} [CommSemiring k] [Group H]
    [AddCommMonoid V] [Module k V] {τ : Representation k H V} (S : Subrepresentation τ) :
    Representation.IsIntertwiningMap τ.dual S.toRepresentation.dual S.toSubmodule.dualRestrict :=
  Representation.IsIntertwiningMap.dualMap ⟨fun _ _ ↦ rfl⟩

section Annihilator

variable {k H V : Type*} [CommSemiring k] [Group H] [AddCommMonoid V] [Module k V]
  {τ : Representation k H V}

/-- The annihilator of a subrepresentation of `τ`, the linear forms vanishing on it, as a
subrepresentation of the dual `τ.dual`. -/
def dualAnnihilator (S : Subrepresentation τ) : Subrepresentation τ.dual where
  toSubmodule := S.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule g φ hφ := by
    rw [Submodule.mem_dualAnnihilator] at hφ ⊢
    intro v hv
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using
      hφ _ (S.apply_mem_toSubmodule g⁻¹ hv)

@[simp]
theorem toSubmodule_dualAnnihilator (S : Subrepresentation τ) :
    S.dualAnnihilator.toSubmodule = S.toSubmodule.dualAnnihilator :=
  (rfl)

/-- A linear form lies in the annihilator of a subrepresentation exactly when it vanishes on it. -/
@[simp]
theorem mem_dualAnnihilator {S : Subrepresentation τ} {φ : Module.Dual k V} :
    φ ∈ S.dualAnnihilator ↔ ∀ v ∈ S, φ v = 0 :=
  Submodule.mem_dualAnnihilator φ

/-- The coannihilator of a subrepresentation of the dual `τ.dual`, the vectors on which all its
linear forms vanish, as a subrepresentation of `τ`. -/
def dualCoannihilator (S : Subrepresentation τ.dual) : Subrepresentation τ where
  toSubmodule := S.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro φ hφ
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using
      hv _ (S.apply_mem_toSubmodule g⁻¹ hφ)

@[simp]
theorem toSubmodule_dualCoannihilator (S : Subrepresentation τ.dual) :
    S.dualCoannihilator.toSubmodule = S.toSubmodule.dualCoannihilator :=
  (rfl)

/-- A vector lies in the coannihilator of a subrepresentation of the dual exactly when all its
linear forms vanish on it. -/
@[simp]
theorem mem_dualCoannihilator {S : Subrepresentation τ.dual} {v : V} :
    v ∈ S.dualCoannihilator ↔ ∀ φ ∈ S, φ v = 0 :=
  Submodule.mem_dualCoannihilator v

end Annihilator

/-- The group-algebra action on a subrepresentation, coerced to the ambient module, is the
original group-algebra action. -/
@[simp]
theorem coe_toRepresentation_asAlgebraHom_apply {k H V : Type*} [CommSemiring k] [Monoid H]
    [AddCommMonoid V] [Module k V] {σ : Representation k H V} (S : Subrepresentation σ)
    (a : MonoidAlgebra k H) (x : S.toSubmodule) :
    ((S.toRepresentation.asAlgebraHom a x : S.toSubmodule) : V) =
      σ.asAlgebraHom a (x : V) :=
  S.subtype.apply_asAlgebraHom a x

section AsSubmoduleEquiv

open scoped MonoidAlgebra

variable {A G W : Type*} [CommSemiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}

/-- The module inclusion attached to `σ.subtype`, corestricted to its image submodule. -/
private noncomputable def asModuleSubtype (σ : Subrepresentation ρ) :
    σ.toRepresentation.asModule →ₗ[A[G]] σ.asSubmodule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule _ _ σ.subtype).codRestrict
    σ.asSubmodule (fun x =>
      (mem_asSubmodule_iff (v := (σ.toRepresentation.asModuleEquiv x : W))).mpr
        (σ.toRepresentation.asModuleEquiv x).property)

/-- The corestricted inclusion evaluates through the two representation/module identifications. -/
private theorem coe_asModuleSubtype_apply (σ : Subrepresentation ρ)
    (x : σ.toRepresentation.asModule) :
    (asModuleSubtype σ x).val = ρ.asModuleEquiv.symm (σ.toRepresentation.asModuleEquiv x).val :=
  (LinearMap.codRestrict_apply _ _ x).trans
    (Representation.IntertwiningMap.equivLinearMapAsModule_apply σ.subtype x)

/-- **The module carried by a subrepresentation is canonically its associated submodule.**
The equivalence identifies both with the same invariant subset of the ambient representation.
Its linear map is the corestriction of the module map attached to `σ.subtype` by
`Representation.IntertwiningMap.equivLinearMapAsModule`. -/
noncomputable def asModuleEquivAsSubmodule (σ : Subrepresentation ρ) :
    σ.toRepresentation.asModule ≃ₗ[A[G]] σ.asSubmodule :=
  LinearEquiv.ofBijective (asModuleSubtype σ)
    ⟨fun x y h => σ.toRepresentation.asModuleEquiv.injective <| Subtype.ext <|
      ρ.asModuleEquiv.symm.injective <| (coe_asModuleSubtype_apply σ x).symm.trans
        ((congrArg Subtype.val h).trans (coe_asModuleSubtype_apply σ y)), fun x =>
      ⟨σ.toRepresentation.asModuleEquiv.symm
        ⟨ρ.asModuleEquiv x.val, (mem_asSubmodule_iff (v := ρ.asModuleEquiv x.val)).mp x.property⟩,
        Subtype.ext <| by
          rw [coe_asModuleSubtype_apply, LinearEquiv.apply_symm_apply]
          exact ρ.asModuleEquiv.symm_apply_apply x.val⟩⟩

@[simp]
theorem coe_asModuleEquivAsSubmodule_apply (σ : Subrepresentation ρ)
    (x : σ.toRepresentation.asModule) :
    (σ.asModuleEquivAsSubmodule x).val =
      (σ.toRepresentation.asModuleEquiv x).val := by
  refine (congrArg Subtype.val (LinearEquiv.ofBijective_apply _
    (hf := σ.asModuleEquivAsSubmodule.bijective) x)).trans ?_
  exact coe_asModuleSubtype_apply σ x

@[simp]
theorem coe_asModuleEquivAsSubmodule_symm_apply (σ : Subrepresentation ρ)
    (x : σ.asSubmodule) :
    (σ.asModuleEquivAsSubmodule.symm x).val =
      _root_.Representation.asModuleEquiv ρ x.val := by
  exact (coe_asModuleEquivAsSubmodule_apply σ (σ.asModuleEquivAsSubmodule.symm x)).symm.trans
    (congrArg Subtype.val (σ.asModuleEquivAsSubmodule.apply_symm_apply x))

/-- **Intertwining maps out of a subrepresentation are module maps out of its submodule**: the
`A[G]`-linear maps out of `σ.asSubmodule`, read through `Subrepresentation.asModuleEquivAsSubmodule`
and `Representation.IntertwiningMap.equivLinearMapAsModule`. -/
noncomputable def intertwiningMapEquivLinearMapAsSubmodule (σ : Subrepresentation ρ)
    {U : Type*} [AddCommMonoid U] [Module A U] (τ : Representation A G U) :
    Representation.IntertwiningMap σ.toRepresentation τ ≃ₗ[A] (σ.asSubmodule →ₗ[A[G]] τ.asModule) :=
  (Representation.IntertwiningMap.equivLinearMapAsModule _ τ).trans
    (LinearEquiv.congrLeft _ A σ.asModuleEquivAsSubmodule)

@[simp]
theorem intertwiningMapEquivLinearMapAsSubmodule_apply (σ : Subrepresentation ρ)
    {U : Type*} [AddCommMonoid U] [Module A U] (τ : Representation A G U)
    (f : Representation.IntertwiningMap σ.toRepresentation τ) (x : σ.asSubmodule) :
    σ.intertwiningMapEquivLinearMapAsSubmodule τ f x =
      Representation.IntertwiningMap.equivLinearMapAsModule _ τ f
        (σ.asModuleEquivAsSubmodule.symm x) :=
  (rfl)

/-- **Membership in a supremum of subrepresentations.** A vector of `ρ`, read in `ρ.asModule`,
lies in the supremum of the `A[G]`-submodules `(σ i).asSubmodule` exactly when it lies in the
supremum of the underlying `A`-submodules `(σ i).toSubmodule`. -/
theorem mem_iSup_asSubmodule_iff {ι : Sort*} {σ : ι → Subrepresentation ρ} {v : W} :
    ρ.asModuleEquiv.symm v ∈ ⨆ i, (σ i).asSubmodule ↔ v ∈ ⨆ i, (σ i).toSubmodule := by
  rw [← Submodule.restrictScalars_mem A, Submodule.restrictScalars_iSup]
  -- `ρ.asModule` is a type synonym for `W` and each `(σ i).asSubmodule` is built from
  -- `(σ i).toSubmodule`, so restricting its scalars to `A` gives back `(σ i).toSubmodule`.
  rfl

end AsSubmoduleEquiv

section AsSubmodule

open scoped MonoidAlgebra

variable {A G W : Type*} [CommRing A] [Monoid G] [AddCommGroup W] [Module A W]
  {ρ : Representation A G W}

/-- A minimal subrepresentation is the same thing as a simple `A[G]`-submodule of the associated
module: the dictionary between the two ways of saying "irreducible constituent".  It is
`isSimpleModule_iff_isAtom` read across `Subrepresentation.subrepresentationSubmoduleOrderIso`. -/
@[simp]
theorem isSimpleModule_asSubmodule_iff {σ : Subrepresentation ρ} :
    IsSimpleModule A[G] σ.asSubmodule ↔ IsAtom σ :=
  isSimpleModule_iff_isAtom.trans (subrepresentationSubmoduleOrderIso.isAtom_iff σ)

end AsSubmodule

section Splitting

variable {A G W : Type*} [Ring A] [Monoid G] [AddCommGroup W] [Module A W]
  {ρ : Representation A G W}

/-- **Complementary subrepresentations split the representation as a direct sum.**  Adding a
vector of `ρ₁` to one of `ρ₂` is a linear isomorphism `ρ₁ × ρ₂ ≃ W` by
`Submodule.prodEquivOfIsCompl`, and it is equivariant because every `ρ g` is additive and
preserves each summand; so `ρ` is the product of the two representations the summands carry.
This is the representation-theoretic content of a complement, of which
`Submodule.prodEquivOfIsCompl` records only the linear part. -/
noncomputable def equivProdOfIsCompl {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂) :
    ρ.Equiv (ρ₁.toRepresentation.prod ρ₂.toRepresentation) :=
  (Representation.Equiv.mk
    (Submodule.prodEquivOfIsCompl ρ₁.toSubmodule ρ₂.toSubmodule (isCompl_toSubmodule.mpr h))
    fun g => LinearMap.ext fun v => by
      simp [toRepresentation_apply]).symm

/-- The splitting is the linear splitting `Submodule.prodEquivOfIsCompl` of the two carriers, read
backwards: it sends a vector to the pair of its components along the complementary submodules. -/
@[simp]
theorem equivProdOfIsCompl_apply {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂) (v : W) :
    equivProdOfIsCompl h v =
      (Submodule.prodEquivOfIsCompl ρ₁.toSubmodule ρ₂.toSubmodule
        (isCompl_toSubmodule.mpr h)).symm v :=
  -- `(rfl)`, not `rfl`: the body of `equivProdOfIsCompl` is not `@[expose]`d, so this must not be
  -- inferred `@[defeq]`.
  (rfl)

/-- The inverse of the splitting adds the two components back together. -/
@[simp]
theorem equivProdOfIsCompl_symm_apply {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂)
    (v : ρ₁.toSubmodule × ρ₂.toSubmodule) :
    (equivProdOfIsCompl h).symm v = (v.1 : W) + (v.2 : W) :=
  -- `(rfl)`, not `rfl`: the body of `equivProdOfIsCompl` is not `@[expose]`d, so this must not be
  -- inferred `@[defeq]`.
  (rfl)

/-- **The projection onto a summand along a complementary subrepresentation intertwines.** For
complementary subrepresentations `ρ₁` and `ρ₂` of `ρ`, the linear projection
`Submodule.projectionOnto` of `W` onto `ρ₁` along `ρ₂` intertwines `ρ` with `ρ₁`. -/
theorem isIntertwiningMap_projectionOnto {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂) :
    Representation.IsIntertwiningMap ρ ρ₁.toRepresentation
      (ρ₁.toSubmodule.projectionOnto ρ₂.toSubmodule (isCompl_toSubmodule.mpr h)) := by
  -- `Submodule.projectionOnto` is the first component of the inverse of
  -- `Submodule.prodEquivOfIsCompl` (`Submodule.prodEquivOfIsCompl_symm_apply`), which
  -- `equivProdOfIsCompl_apply` identifies with the splitting.
  obtain ⟨f, hf⟩ : ∃ f : Representation.IntertwiningMap ρ ρ₁.toRepresentation,
      f.toLinearMap = ρ₁.toSubmodule.projectionOnto ρ₂.toSubmodule (isCompl_toSubmodule.mpr h) :=
    ⟨(Representation.IntertwiningMap.fst A ρ₁.toRepresentation ρ₂.toRepresentation).comp
      (equivProdOfIsCompl h).toIntertwiningMap,
      LinearMap.ext fun v => by simp [equivProdOfIsCompl_apply]⟩
  exact hf ▸ ⟨f.isIntertwining⟩

end Splitting

section FG

variable {A G W : Type*} [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}

/-- The finitely generated subrepresentations form a join-semilattice: the join of two of them,
taken in `Subrepresentation ρ`, carries the sum of two finitely generated submodules. This is the
counterpart of Mathlib's instance on `{P : Submodule A W // P.FG}`, and it makes the finitely
generated subrepresentations a directed index category. -/
instance instSemilatticeSupFG : SemilatticeSup {σ : Subrepresentation ρ // σ.toSubmodule.FG} :=
  Subtype.semilatticeSup fun _ _ h₁ h₂ ↦ h₁.sup h₂

instance instInhabitedFG : Inhabited {σ : Subrepresentation ρ // σ.toSubmodule.FG} :=
  ⟨⟨⊥, Submodule.fg_bot⟩⟩

end FG

section Res

variable {k : Type*} [Semiring k] {H K : Type*} [Monoid H] [Monoid K]
  {V : Type*} [AddCommMonoid V] [Module k V] {ρ : Representation k K V}

/-- The restriction of a subrepresentation of `ρ` along a monoid homomorphism `f`: the same
underlying submodule, as a subrepresentation of `ρ.comp f`. Its body is exposed so that
`Subrepresentation.toRepresentation_res` can be stated. -/
@[expose] def res (f : H →* K) (σ : Subrepresentation ρ) : Subrepresentation (ρ.comp f) where
  toSubmodule := σ.toSubmodule
  apply_mem_toSubmodule h _ hv := σ.apply_mem_toSubmodule (f h) hv

/-- Restriction along a monoid homomorphism keeps the underlying submodule. -/
@[simp]
theorem toSubmodule_res (f : H →* K) (σ : Subrepresentation ρ) :
    (σ.res f).toSubmodule = σ.toSubmodule :=
  rfl

/-- Restriction along a monoid homomorphism keeps the underlying set. -/
@[simp]
theorem coe_res (f : H →* K) (σ : Subrepresentation ρ) : (σ.res f : Set V) = σ :=
  rfl

/-- A vector lies in the restriction of `σ` along `f` exactly when it lies in `σ`. -/
@[simp]
theorem mem_res {f : H →* K} {σ : Subrepresentation ρ} {v : V} : v ∈ σ.res f ↔ v ∈ σ :=
  Iff.rfl

/-- The representation carried by the restriction of `σ` along `f` is the restriction along `f` of
the representation carried by `σ`. -/
theorem toRepresentation_res (f : H →* K) (σ : Subrepresentation ρ) :
    (σ.res f).toRepresentation = σ.toRepresentation.comp f :=
  rfl

end Res

end Subrepresentation

namespace Representation

section Cyclic

open scoped MonoidAlgebra

variable {A G W : Type*} [CommSemiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}

/-- The span of the orbit of a vector is invariant under the representation. -/
theorem apply_mem_span_range_apply (v : W) (g : G) {w : W}
    (hw : w ∈ Submodule.span A (Set.range fun h : G ↦ ρ h v)) :
    ρ g w ∈ Submodule.span A (Set.range fun h : G ↦ ρ h v) := by
  refine (Submodule.map_span_le (ρ g) _ _).2 ?_ (Submodule.mem_map_of_mem hw)
  rintro _ ⟨h, rfl⟩
  exact Submodule.subset_span ⟨g * h, by simp⟩

variable (ρ) in
/-- The subrepresentation `A[G] · v` generated by a vector `v`: the cyclic `A[G]`-submodule of
`ρ.asModule` spanned by `v`, as a subrepresentation. -/
noncomputable def cyclicSubrepresentation (v : W) : Subrepresentation ρ :=
  Subrepresentation.ofSubmodule' (Submodule.span A[G] {v})

/-- The `A[G]`-submodule carried by `A[G] · v` is the cyclic submodule spanned by `v`. -/
theorem asSubmodule_cyclicSubrepresentation (v : W) :
    (cyclicSubrepresentation ρ v).asSubmodule =
      (Submodule.span A[G] {v} : Submodule A[G] ρ.asModule) :=
  Subrepresentation.subrepresentationSubmoduleOrderIso.right_inv _

/-- A vector lies in the subrepresentation it generates. -/
@[simp]
theorem mem_cyclicSubrepresentation_self (v : W) : v ∈ cyclicSubrepresentation ρ v :=
  Subrepresentation.mem_ofSubmodule'_iff.mpr
    (Submodule.mem_span_singleton_self (M := ρ.asModule) v)

/-- **`A[G] · v` is the least subrepresentation containing `v`.** -/
@[simp]
theorem cyclicSubrepresentation_le_iff {v : W} {σ : Subrepresentation ρ} :
    cyclicSubrepresentation ρ v ≤ σ ↔ v ∈ σ :=
  ⟨fun h ↦ h (mem_cyclicSubrepresentation_self v), fun h w hw ↦ by
    rw [← Subrepresentation.mem_asSubmodule_iff, asSubmodule_cyclicSubrepresentation] at hw
    rw [← Subrepresentation.mem_asSubmodule_iff] at h ⊢
    exact (Submodule.span_singleton_le_iff_mem (M := ρ.asModule) v _).mpr h hw⟩

/-- The vectors of `A[G] · v` are the `A`-linear combinations of the translates `ρ g v`. -/
theorem toSubmodule_cyclicSubrepresentation (v : W) :
    (cyclicSubrepresentation ρ v).toSubmodule = Submodule.span A (Set.range fun g ↦ ρ g v) := by
  refine le_antisymm ?_ (Submodule.span_le.2 <| Set.range_subset_iff.2 fun g ↦
    (cyclicSubrepresentation ρ v).apply_mem_toSubmodule g (mem_cyclicSubrepresentation_self v))
  let σ : Subrepresentation ρ :=
    ⟨Submodule.span A (Set.range fun g ↦ ρ g v), fun g _ hw ↦ ρ.apply_mem_span_range_apply v g hw⟩
  exact cyclicSubrepresentation_le_iff (σ := σ).2 <|
    Submodule.subset_span ⟨1, by simp⟩

/-- A vector lies in `A[G] · v` exactly when it is an `A`-linear combination of translates of `v`.
-/
theorem mem_cyclicSubrepresentation_iff {v w : W} :
    w ∈ cyclicSubrepresentation ρ v ↔ w ∈ Submodule.span A (Set.range fun g ↦ ρ g v) := by
  rw [← Subrepresentation.mem_toSubmodule, toSubmodule_cyclicSubrepresentation]

end Cyclic

end Representation

namespace MonoidHom

variable {k : Type*} [Semiring k] {H K : Type*} [Monoid H] [Monoid K]
  {V : Type*} [AddCommMonoid V] [Module k V]

/-- Restriction along a surjective monoid homomorphism identifies invariant subspaces: a subspace
invariant under `ρ ∘ f` is invariant under `ρ`, because `f` is onto.  Both directions keep the
underlying submodule. -/
def resSubrepresentationOrderIso (f : H →* K) (hf : Function.Surjective f)
    (ρ : Representation k K V) :
    Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun h v hv ↦ by
        obtain ⟨g, rfl⟩ := hf h
        exact S.apply_mem_toSubmodule g hv }
  invFun S := S.res f
  left_inv S := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := by rfl

/-- The forward invariant-subspace correspondence preserves the underlying submodule. -/
@[simp]
theorem resSubrepresentationOrderIso_apply_toSubmodule (f : H →* K) (hf : Function.Surjective f)
    (ρ : Representation k K V) (S : Subrepresentation (ρ.comp f)) :
    (MonoidHom.resSubrepresentationOrderIso f hf ρ S).toSubmodule = S.toSubmodule :=
  (rfl)

/-- The inverse invariant-subspace correspondence preserves the underlying submodule. -/
@[simp]
theorem resSubrepresentationOrderIso_symm_apply_toSubmodule (f : H →* K)
    (hf : Function.Surjective f) (ρ : Representation k K V) (S : Subrepresentation ρ) :
    ((MonoidHom.resSubrepresentationOrderIso f hf ρ).symm S).toSubmodule = S.toSubmodule :=
  (rfl)

end MonoidHom

/-- **Invariance under a spanning monoid is invariance under the whole algebra.** If the image of
`φ : H →* B` spans the `R`-algebra `B`, a submodule is invariant under the restriction along `φ`
of an algebra action `F` exactly when it is invariant under every `F b`. -/
theorem AlgHom.mem_invtSubmodule_toMonoidHom_comp_iff_of_span_eq_top {R B H M : Type*}
    [CommSemiring R] [Semiring B] [Algebra R B] [Monoid H] [AddCommMonoid M] [Module R M]
    (F : B →ₐ[R] Module.End R M) (φ : H →* B) (hφ : Submodule.span R (Set.range φ) = ⊤)
    (p : Submodule R M) :
    p ∈ Representation.invtSubmodule ((F : B →* Module.End R M).comp φ) ↔
      ∀ b, p ∈ Module.End.invtSubmodule (F b) := by
  -- The restricted action acts by `F (φ g)`.
  simp only [Representation.mem_invtSubmodule, MonoidHom.comp_apply, AlgHom.coe_toMonoidHom]
  refine ⟨fun hp b ↦ ?_, fun hp g ↦ hp (φ g)⟩
  -- The elements of `B` whose action preserves `p` form a submodule containing the image of `φ`.
  have hmem (c : B) : c ∈ (p.compatibleMaps p).comap F.toLinearMap ↔
      p ∈ Module.End.invtSubmodule (F c) := by
    rw [Submodule.mem_comap, AlgHom.coe_toLinearMap, Submodule.mem_compatibleMaps,
      Module.End.mem_invtSubmodule]
  have hle : Submodule.span R (Set.range φ) ≤ (p.compatibleMaps p).comap F.toLinearMap :=
    Submodule.span_le.2 <| Set.range_subset_iff.2 fun g ↦ (hmem (φ g)).2 (hp g)
  exact (hmem b).1 ((hφ ▸ hle) (Submodule.mem_top (x := b)))

section Irreducible

variable {k : Type*} [Field k] {H K : Type*} [Monoid H] [Monoid K]
  {V : Type*} [AddCommGroup V] [Module k V]

/-- Restriction along a surjective monoid homomorphism preserves irreducibility: irreducibility is
simplicity of the lattice of invariant subspaces, and `MonoidHom.resSubrepresentationOrderIso`
identifies the two lattices. -/
@[simp]
theorem MonoidHom.isIrreducible_comp_surjective_iff (f : H →* K) (hf : Function.Surjective f)
    (ρ : Representation k K V) :
    Representation.IsIrreducible (ρ.comp f) ↔ Representation.IsIrreducible ρ :=
  (f.resSubrepresentationOrderIso hf ρ).isSimpleOrder_iff

/-- Restriction along a monoid isomorphism preserves irreducibility. -/
@[simp]
theorem MulEquiv.isIrreducible_comp_equiv_iff (e : H ≃* K) (ρ : Representation k K V) :
    Representation.IsIrreducible (ρ.comp (e : H →* K)) ↔ Representation.IsIrreducible ρ :=
  e.toMonoidHom.isIrreducible_comp_surjective_iff e.surjective ρ

end Irreducible
