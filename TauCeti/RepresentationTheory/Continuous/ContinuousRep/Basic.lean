/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.LinearAlgebra.Dual.FiniteProjective
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Units
public import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Jointly continuous representations

A *continuous representation* of a monoid `Γ` with a topology on an `A`-module `M` with a topology,
in the sense used for Galois representations, is a linear representation `Γ →* End_A M` whose
action map `Γ × M → M` is jointly continuous. This is stronger than asking each operator to be
continuous, which is what Mathlib's `ContRepresentation` records: for instance the multiplication
action of `ℤ_ℓˣ` on `ℚ_ℓ` with the discrete topology has continuous operators but is not jointly
continuous. This file packages such an action as `TauCeti.ContinuousRep Γ A M` and develops the
elementary operations needed to build integral models of `ℓ`-adic representations: isomorphisms,
the trivial representation, products, invariant submodules and quotients, the line attached to a
continuous character, extension of scalars, and the contragredient representation. Forgetting joint
continuity is injective, and its image in Mathlib's `ContRepresentation` consists of the jointly
continuous actions (`TauCeti.ContinuousRep.ofContRepresentation`).

The typical module is a finite module `M` over a topological ring `A`, carrying its module
topology (`IsModuleTopology A M`). Over such modules every linear map is continuous, so an
equivariant linear equivalence is automatically an isomorphism of continuous representations
(`TauCeti.ContinuousRep.Iso.ofEquiv`). Joint continuity on such a module can be checked
on the orbits of a finite generating family
(`IsModuleTopology.continuous_linearMap_apply_iff_of_span_eq_top`) or, on a free module, on the
matrix coefficients in a basis (`TauCeti.ContinuousRep.continuous_toMatrix` and its converse
`TauCeti.ModuleTopology.continuous_linearMap_apply_iff_continuous_toMatrix`). Extension of
scalars along a continuous ring map `A → B` gives `B ⊗[A] M` its `B`-module topology; the
base-changed action is again jointly continuous because the tensors `1 ⊗ m` of a finite
generating family of `M` generate `B ⊗[A] M` and have continuous orbits.
Likewise, a group acting on a finite projective module acts jointly continuously on its linear
dual with the module topology: a finite dual basis writes each functional through its values on
finitely many vectors.

## Main definitions

* `TauCeti.ContinuousRep Γ A M`: a representation of `Γ` on `M` whose action is jointly
  continuous.
* `TauCeti.ContinuousRep.toContRepresentation` and `TauCeti.ContinuousRep.ofContRepresentation`:
  conversion between `ContinuousRep` and jointly continuous Mathlib `ContRepresentation`s.
* `TauCeti.ContinuousRep.trivial`: the trivial representation.
* `TauCeti.ContinuousRep.subrepresentation`: restriction to an invariant submodule with the
  subspace topology.
* `TauCeti.ContinuousRep.quotient`: descent to the quotient by an invariant submodule with the
  quotient topology.
* `TauCeti.ContinuousRep.prod`: the componentwise action on a product.
* `TauCeti.ContinuousRep.Iso`: equivariant continuous linear equivalences, with `refl`, `symm`
  and `trans`.
* `TauCeti.ContinuousRep.ofCharacter`: the rank-one representation of a continuous character
  `Γ →ₜ* Aˣ`.
* `TauCeti.ContinuousRep.baseChange`: extension of scalars `B ⊗[A] M` along a continuous
  coefficient map, using `Representation.baseChange`.
* `TauCeti.ContinuousRep.Iso.baseChange`: extension of scalars of an isomorphism.
* `TauCeti.ContinuousRep.baseChangeSelfIso` and `TauCeti.ContinuousRep.baseChangeTransIso`:
  extension of scalars to `A` itself is trivial, and extension along `A → B → C` is extension
  along `A → C`.
* `TauCeti.ContinuousRep.baseChangeOfCharacterIso`: the base change of a character line is the
  line of the character composed with `Aˣ → Bˣ`.
* `TauCeti.ContinuousRep.baseChangeTrivialIso`: the base change of the trivial representation is
  the trivial representation.
* `TauCeti.ContinuousRep.dual`: the contragredient representation on `Module.Dual A M`, using
  `Representation.dual`.

## Main results

* `TauCeti.ContinuousRep.continuous_apply`: each operator of a continuous representation is
  continuous.
* `TauCeti.ContinuousRep.toContRepresentation_injective` and
  `TauCeti.ContinuousRep.range_toContRepresentation`: a continuous representation is determined
  by its operators, and the Mathlib continuous representations arising this way are those with
  jointly continuous action.
* `TauCeti.ContinuousRep.finite_range`: a continuous representation on a finite carrier has
  finite image.
* `TauCeti.ContinuousRep.continuous_toMatrix`: the matrix coefficients in a finite basis are
  continuous.
* `TauCeti.ContinuousRep.nonempty_iso_ofCharacter_iff`: two character lines are isomorphic
  exactly when the characters agree.
* `TauCeti.ContinuousRep.baseChangeTransIso_trans_baseChangeTransIso`: the two identifications
  of a threefold scalar extension `A → B → C → D` with the extension along `A → D` agree.

## Implementation notes

`TauCeti.ContinuousRep.Iso` is stated over a semiring, for arbitrary topologies on the carriers.
Mathlib's `ContRepresentation.Equiv` is attached to `ContRepresentation`, which asks for a ring and
topological additive groups.

The topology on a base change `B ⊗[A] M` is an instance argument together with
`IsModuleTopology B (B ⊗[A] M)`, as for any module topology in Mathlib, so a consumer may supply
`moduleTopology B (B ⊗[A] M)` or any topology known to coincide with it. Only finiteness of `M`
is needed for the base-changed action to be continuous; projectivity plays no role here. The
topology on the dual `Module.Dual A M` is supplied the same way; there `M` is finite projective.

When the target ring is `B = ℤ`, whatever `A` is, this runs into Mathlib's `ℤ`-module diamond on
tensor products: written in a statement, `[IsModuleTopology ℤ (ℤ ⊗[A] M)]` elaborates with the
additive group's `ℤ`-action, while `TauCeti.ContinuousRep.baseChange` asks for it with the tensor
product's left action `TensorProduct.leftHasSMul`. The two actions agree, but not at instance
transparency, so `ρ.baseChange ℤ` fails to synthesize the hypothesis, and so does every declaration
here that extends scalars to `ℤ`, such as `baseChangeSelfIso` for `A = ℤ`. The same happens when
the topology is given as `moduleTopology ℤ (ℤ ⊗[A] M)`. Installing `TensorProduct.leftHasSMul` as
a local `SMul ℤ (ℤ ⊗[A] M)` instance before forming `moduleTopology ℤ (ℤ ⊗[A] M)` or stating
`[IsModuleTopology ℤ (ℤ ⊗[A] M)]` avoids this. Extending scalars from `A = ℤ` to another ring,
such as `ℚ`, does not meet this diamond.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- **A jointly continuous representation.** A linear representation of the monoid `Γ` with a
topology on the `A`-module `M` with a topology, whose action map `Γ × M → M` is continuous. The
structure assumes no further compatibility of the topologies with the algebraic structure
(`A` carries no topology here); the declarations that need more state it themselves. -/
structure ContinuousRep (Γ A M : Type*) [Monoid Γ] [TopologicalSpace Γ] [Semiring A]
    [AddCommMonoid M] [Module A M] [TopologicalSpace M] where
  /-- The underlying linear representation. -/
  toRepresentation : Representation A Γ M
  /-- The action map `Γ × M → M` is jointly continuous. -/
  continuous_action : Continuous fun p : Γ × M => toRepresentation p.1 p.2

namespace ContinuousRep

section Basic

variable {Γ A M N P : Type*} [Monoid Γ] [TopologicalSpace Γ] [Semiring A]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [AddCommMonoid N] [Module A N] [TopologicalSpace N]
  [AddCommMonoid P] [Module A P] [TopologicalSpace P]

instance : FunLike (ContinuousRep Γ A M) Γ (M →ₗ[A] M) where
  coe ρ := ρ.toRepresentation
  coe_injective ρ σ h := by
    cases ρ
    cases σ
    congr
    exact DFunLike.coe_injective h

instance : MonoidHomClass (ContinuousRep Γ A M) Γ (M →ₗ[A] M) where
  map_mul ρ := ρ.toRepresentation.map_mul
  map_one ρ := ρ.toRepresentation.map_one

@[simp]
theorem coe_toRepresentation (ρ : ContinuousRep Γ A M) : ⇑ρ.toRepresentation = ρ :=
  (rfl)

@[simp]
theorem coe_mk (ρ : Representation A Γ M) (hρ : Continuous fun p : Γ × M => ρ p.1 p.2) :
    ⇑(⟨ρ, hρ⟩ : ContinuousRep Γ A M) = ρ :=
  (rfl)

/-- Two continuous representations with the same action are equal. -/
@[ext]
theorem ext {ρ σ : ContinuousRep Γ A M} (h : ∀ g x, ρ g x = σ g x) : ρ = σ :=
  DFunLike.ext _ _ fun g => LinearMap.ext (h g)

/-- **Joint continuity in the form `fun_prop` uses.** If `f : X → Γ` and `g : X → M` are
continuous, then so is `x ↦ ρ (f x) (g x)`. This is the field `continuous_action`, stated through
the coercion `⇑ρ` in compositional form. -/
@[fun_prop]
theorem _root_.Continuous.continuousRep_apply {X : Type*} [TopologicalSpace X]
    (ρ : ContinuousRep Γ A M) {f : X → Γ} {g : X → M} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => ρ (f x) (g x) :=
  ρ.continuous_action.comp (hf.prodMk hg)

/-- **Each operator of a jointly continuous representation is continuous.** -/
@[fun_prop]
theorem continuous_apply (ρ : ContinuousRep Γ A M) (g : Γ) : Continuous (ρ g) := by
  fun_prop

/-- The orbit map `g ↦ ρ g x` of a jointly continuous representation is continuous. -/
@[fun_prop]
theorem continuous_orbit (ρ : ContinuousRep Γ A M) (x : M) : Continuous fun g => ρ g x := by
  fun_prop

variable (Γ A M) in
/-- **The trivial continuous representation**: every element of `Γ` acts as the identity of
`M`. -/
def trivial : ContinuousRep Γ A M where
  toRepresentation := Representation.trivial A Γ M
  continuous_action := continuous_snd

variable (Γ A M) in
instance : Inhabited (ContinuousRep Γ A M) := ⟨trivial Γ A M⟩

@[simp]
theorem toRepresentation_trivial :
    (trivial Γ A M).toRepresentation = Representation.trivial A Γ M :=
  (rfl)

@[simp]
theorem trivial_apply (g : Γ) (x : M) : trivial Γ A M g x = x :=
  (rfl)

/-- Every element of `Γ` acts as the identity operator in the trivial representation. -/
theorem trivial_apply_eq_id (g : Γ) : trivial Γ A M g = LinearMap.id :=
  Representation.isTrivial_def (Representation.trivial A Γ M) g

/-- **Finite image.** A continuous representation on a finite carrier takes only finitely many
values. -/
theorem finite_range [Finite M] (ρ : ContinuousRep Γ A M) :
    (Set.range (ρ : Γ → Module.End A M)).Finite :=
  have : Finite (Module.End A M) := .of_injective _ DFunLike.coe_injective
  Set.toFinite _

section Subquotient

/-- Restriction to an invariant submodule, with its inherited topology. -/
def subrepresentation (ρ : ContinuousRep Γ A M) (W : Submodule A M)
    (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W) : ContinuousRep Γ A W where
  toRepresentation := ρ.toRepresentation.subrepresentation W hW
  continuous_action := (ρ.continuous_action.comp
    (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))).subtype_mk _

@[simp]
theorem toRepresentation_subrepresentation (ρ : ContinuousRep Γ A M) (W : Submodule A M)
    (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W) :
    (ρ.subrepresentation W hW).toRepresentation = ρ.toRepresentation.subrepresentation W hW :=
  (rfl)

@[simp]
theorem coe_subrepresentation_apply (ρ : ContinuousRep Γ A M) (W : Submodule A M)
    (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W) (g : Γ) (x : W) :
    (ρ.subrepresentation W hW g x : M) = ρ g x :=
  (rfl)

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] [TopologicalSpace V]

/-- Descent to the quotient by an invariant submodule, with its quotient topology. -/
def quotient [ContinuousAdd V] (ρ : ContinuousRep Γ R V) (W : Submodule R V)
    (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W) : ContinuousRep Γ R (V ⧸ W) where
  toRepresentation := ρ.toRepresentation.quotient W hW
  continuous_action := by
    rw [← (IsOpenQuotientMap.id.prodMap W.isOpenQuotientMap_mkQ).continuous_comp_iff]
    exact W.continuous_mkQ.comp ρ.continuous_action

@[simp]
theorem toRepresentation_quotient [ContinuousAdd V] (ρ : ContinuousRep Γ R V)
    (W : Submodule R V) (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W) :
    (ρ.quotient W hW).toRepresentation = ρ.toRepresentation.quotient W hW :=
  (rfl)

@[simp]
theorem quotient_apply_mk [ContinuousAdd V] (ρ : ContinuousRep Γ R V)
    (W : Submodule R V) (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W) (g : Γ) (x : V) :
    ρ.quotient W hW g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) :=
  (rfl)

end Subquotient

section Constructions

/-- **The product of two continuous representations**: `Γ` acts componentwise on `M × N`, with
the product topology. -/
noncomputable def prod (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) :
    ContinuousRep Γ A (M × N) where
  toRepresentation := ρ.toRepresentation.prod σ.toRepresentation
  -- `Representation.prod` acts on `(x, y)` by `(ρ g x, σ g y)` by definition, and is stated with
  -- `LinearMap.prodMap`, which `fun_prop` does not unfold.
  continuous_action := show Continuous fun p : Γ × (M × N) => (ρ p.1 p.2.1, σ p.1 p.2.2) by
    fun_prop

@[simp]
theorem toRepresentation_prod (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) :
    (ρ.prod σ).toRepresentation = ρ.toRepresentation.prod σ.toRepresentation :=
  (rfl)

@[simp]
theorem prod_apply (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) (g : Γ) (x : M × N) :
    ρ.prod σ g x = (ρ g x.1, σ g x.2) :=
  (rfl)

end Constructions

section ContRepresentation

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] [TopologicalSpace V]
  [IsTopologicalAddGroup V]

/-- The Mathlib continuous representation underlying a jointly continuous representation: each
operator, which is continuous by `TauCeti.ContinuousRep.continuous_apply`. -/
def toContRepresentation (ρ : ContinuousRep Γ R V) : ContRepresentation R Γ V :=
  .ofMonoidHom
    { toFun g := ⟨ρ g, ρ.continuous_apply g⟩
      map_one' := by ext; simp
      map_mul' g h := by ext; simp }

@[simp]
theorem toContRepresentation_apply (ρ : ContinuousRep Γ R V) (g : Γ) (x : V) :
    ρ.toContRepresentation g x = ρ g x :=
  (rfl)

/-- **A jointly continuous representation is determined by its operators.** -/
theorem toContRepresentation_injective :
    Function.Injective (toContRepresentation : ContinuousRep Γ R V → ContRepresentation R Γ V) :=
  fun _ _ h => ext fun g x => by simpa using congr($h g x)

/-- Two continuous representations have equal underlying `ContRepresentation`s if and only if they
are equal. -/
@[simp]
theorem toContRepresentation_inj {ρ σ : ContinuousRep Γ R V} :
    ρ.toContRepresentation = σ.toContRepresentation ↔ ρ = σ :=
  toContRepresentation_injective.eq_iff

/-- Forgetting from `ContinuousRep` to `ContRepresentation` and then to `Representation` gives the
underlying algebraic representation. -/
@[simp]
theorem toRepresentation_toContRepresentation (ρ : ContinuousRep Γ R V) :
    ρ.toContRepresentation.toRepresentation = ρ.toRepresentation := by
  ext g x
  exact ρ.toContRepresentation_apply g x

/-- Builds a `ContinuousRep` from a `ContRepresentation` whose action map `Γ × V → V` is jointly
continuous. -/
def ofContRepresentation (π : ContRepresentation R Γ V)
    (hπ : Continuous fun p : Γ × V => π p.1 p.2) : ContinuousRep Γ R V where
  toRepresentation := π.toRepresentation
  continuous_action := hπ

@[simp]
theorem ofContRepresentation_apply (π : ContRepresentation R Γ V)
    (hπ : Continuous fun p : Γ × V => π p.1 p.2) (g : Γ) (x : V) :
    ofContRepresentation π hπ g x = π g x :=
  (rfl)

@[simp]
theorem toRepresentation_ofContRepresentation (π : ContRepresentation R Γ V)
    (hπ : Continuous fun p : Γ × V => π p.1 p.2) :
    (ofContRepresentation π hπ).toRepresentation = π.toRepresentation :=
  (rfl)

@[simp]
theorem toContRepresentation_ofContRepresentation (π : ContRepresentation R Γ V)
    (hπ : Continuous fun p : Γ × V => π p.1 p.2) :
    (ofContRepresentation π hπ).toContRepresentation = π :=
  DFunLike.ext _ _ fun _ => ContinuousLinearMap.ext fun _ => by simp

@[simp]
theorem ofContRepresentation_toContRepresentation (ρ : ContinuousRep Γ R V)
    (h : Continuous fun p : Γ × V => ρ.toContRepresentation p.1 p.2) :
    ofContRepresentation ρ.toContRepresentation h = ρ := by
  ext g x
  simp

/-- A `ContRepresentation` lies in the image of `toContRepresentation` if and only if its action
`Γ × V → V` is jointly continuous. -/
theorem mem_range_toContRepresentation_iff {π : ContRepresentation R Γ V} :
    π ∈ Set.range (toContRepresentation : ContinuousRep Γ R V → ContRepresentation R Γ V) ↔
      Continuous fun p : Γ × V => π p.1 p.2 :=
  ⟨fun ⟨ρ, hρ⟩ =>
      hρ ▸ ρ.continuous_action.congr fun p => (ρ.toContRepresentation_apply p.1 p.2).symm,
    fun hπ => ⟨ofContRepresentation π hπ, toContRepresentation_ofContRepresentation π hπ⟩⟩

/-- **The image of the forgetful map to `ContRepresentation`.** A Mathlib continuous
representation, whose operators are merely continuous, comes from a jointly continuous
representation exactly when its action map `Γ × V → V` is continuous. -/
@[simp]
theorem range_toContRepresentation :
    Set.range (toContRepresentation : ContinuousRep Γ R V → ContRepresentation R Γ V) =
      {π | Continuous fun p : Γ × V => π p.1 p.2} :=
  Set.ext fun _ => mem_range_toContRepresentation_iff

variable (Γ R V) in
@[simp]
theorem toContRepresentation_trivial :
    (trivial Γ R V).toContRepresentation = ContRepresentation.trivial R Γ V :=
  (rfl)

end ContRepresentation

section Matrix

variable {R V ι : Type*} [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]
  [AddCommMonoid V] [Module R V] [TopologicalSpace V] [IsModuleTopology R V] [Fintype ι]
  [DecidableEq ι]

/-- **The matrix coefficients of a continuous representation are continuous.** In a finite basis
`b` of a module with its module topology, `g ↦ LinearMap.toMatrix b b (ρ g)` is continuous.
Conversely, by `TauCeti.ModuleTopology.continuous_linearMap_apply_iff_continuous_toMatrix`, a
linear representation whose matrix coefficients are continuous is jointly continuous. -/
theorem continuous_toMatrix (ρ : ContinuousRep Γ R V) (b : Module.Basis ι R V) :
    Continuous fun g => LinearMap.toMatrix b b (ρ g) :=
  (ModuleTopology.continuous_linearMap_apply_iff_continuous_toMatrix b b ρ).mp ρ.continuous_action

end Matrix

/-- **An isomorphism of continuous representations**: an equivariant linear equivalence that is
a homeomorphism. -/
structure Iso (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) extends
    toRepresentationEquiv : ρ.toRepresentation.Equiv σ.toRepresentation,
    toContinuousLinearEquiv : M ≃L[A] N

/-- The equivalence of linear representations underlying an isomorphism of continuous
representations. -/
add_decl_doc Iso.toRepresentationEquiv

/-- The continuous linear equivalence underlying an isomorphism of continuous representations. -/
add_decl_doc Iso.toContinuousLinearEquiv

namespace Iso

variable {ρ : ContinuousRep Γ A M} {σ : ContinuousRep Γ A N} {τ : ContinuousRep Γ A P}

instance : EquivLike (Iso ρ σ) M N where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e f h _ := by
    rcases e with ⟨e, _, _⟩
    rcases f with ⟨f, _, _⟩
    congr
    exact Representation.Equiv.ext h

instance : ContinuousLinearEquivClass (Iso ρ σ) A M N where
  map_add e := e.map_add'
  map_smulₛₗ e := e.map_smul'
  map_continuous e := e.continuous_toFun
  inv_continuous e := e.continuous_invFun

@[simp]
theorem coe_toRepresentationEquiv (e : Iso ρ σ) : ⇑e.toRepresentationEquiv = e :=
  (rfl)

theorem coe_toContinuousLinearEquiv (e : Iso ρ σ) : ⇑e.toContinuousLinearEquiv = e :=
  (rfl)

@[ext]
theorem ext {e f : Iso ρ σ} (h : ∀ x, e x = f x) : e = f :=
  DFunLike.ext _ _ h

/-- **An isomorphism of continuous representations is equivariant.** -/
theorem isIntertwining (e : Iso ρ σ) (g : Γ) (x : M) : e (ρ g x) = σ g (e x) :=
  Representation.IntertwiningMap.isIntertwining _ _ e.toRepresentationEquiv.toIntertwiningMap g x

section ofEquiv

variable [TopologicalSpace A] [IsModuleTopology A M] [IsModuleTopology A N]

/-- **Automatic continuity of isomorphisms.** For modules with their module topologies, an
equivalence of the underlying linear representations is an isomorphism of continuous
representations. -/
def ofEquiv (e : ρ.toRepresentation.Equiv σ.toRepresentation) : Iso ρ σ :=
  haveI := IsModuleTopology.toContinuousAdd A M
  haveI := IsModuleTopology.toContinuousAdd A N
  { toRepresentationEquiv := e
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

@[simp]
theorem ofEquiv_apply (e : ρ.toRepresentation.Equiv σ.toRepresentation) (x : M) :
    ofEquiv e x = e x :=
  (rfl)

@[simp]
theorem toRepresentationEquiv_ofEquiv (e : ρ.toRepresentation.Equiv σ.toRepresentation) :
    (ofEquiv e).toRepresentationEquiv = e :=
  (rfl)

end ofEquiv

variable (ρ) in
/-- The identity isomorphism of a continuous representation. -/
@[refl]
def refl : Iso ρ ρ where
  toRepresentationEquiv := .refl ρ.toRepresentation
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

/-- The inverse of an isomorphism of continuous representations. -/
@[symm]
def symm (e : Iso ρ σ) : Iso σ ρ where
  toRepresentationEquiv := e.toRepresentationEquiv.symm
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun

/-- The composite of two isomorphisms of continuous representations. -/
@[trans]
def trans (e : Iso ρ σ) (f : Iso σ τ) : Iso ρ τ where
  toRepresentationEquiv := e.toRepresentationEquiv.trans f.toRepresentationEquiv
  continuous_toFun := f.continuous_toFun.comp e.continuous_toFun
  continuous_invFun := e.continuous_invFun.comp f.continuous_invFun

@[simp]
theorem refl_apply (x : M) : refl ρ x = x :=
  (rfl)

@[simp]
theorem trans_apply (e : Iso ρ σ) (f : Iso σ τ) (x : M) : e.trans f x = f (e x) :=
  (rfl)

@[simp]
theorem symm_apply_apply (e : Iso ρ σ) (x : M) : e.symm (e x) = x :=
  e.left_inv x

@[simp]
theorem apply_symm_apply (e : Iso ρ σ) (y : N) : e (e.symm y) = y :=
  e.right_inv y

@[simp]
theorem symm_symm (e : Iso ρ σ) : e.symm.symm = e :=
  ext fun x ↦ e.symm.injective <|
    (e.symm.apply_symm_apply x).trans (e.symm_apply_apply x).symm

@[simp]
theorem refl_symm : (refl ρ).symm = refl ρ :=
  ext fun _ ↦ (rfl)

@[simp]
theorem trans_refl (e : Iso ρ σ) : e.trans (refl σ) = e :=
  ext fun _ ↦ (rfl)

@[simp]
theorem refl_trans (e : Iso ρ σ) : (refl ρ).trans e = e :=
  ext fun _ ↦ (rfl)

@[simp]
theorem self_trans_symm (e : Iso ρ σ) : e.trans e.symm = refl ρ :=
  ext e.symm_apply_apply

@[simp]
theorem symm_trans_self (e : Iso ρ σ) : e.symm.trans e = refl σ :=
  ext e.apply_symm_apply

@[simp]
theorem toRepresentationEquiv_refl :
    (refl ρ).toRepresentationEquiv = .refl ρ.toRepresentation :=
  (rfl)

@[simp]
theorem toRepresentationEquiv_symm (e : Iso ρ σ) :
    e.symm.toRepresentationEquiv = e.toRepresentationEquiv.symm :=
  (rfl)

@[simp]
theorem toRepresentationEquiv_trans (e : Iso ρ σ) (f : Iso σ τ) :
    (e.trans f).toRepresentationEquiv = e.toRepresentationEquiv.trans f.toRepresentationEquiv :=
  (rfl)

@[simp]
theorem toContinuousLinearEquiv_refl :
    (refl ρ).toContinuousLinearEquiv = .refl A M :=
  (rfl)

@[simp]
theorem toContinuousLinearEquiv_symm (e : Iso ρ σ) :
    e.symm.toContinuousLinearEquiv = e.toContinuousLinearEquiv.symm :=
  (rfl)

@[simp]
theorem toContinuousLinearEquiv_trans (e : Iso ρ σ) (f : Iso σ τ) :
    (e.trans f).toContinuousLinearEquiv =
      e.toContinuousLinearEquiv.trans f.toContinuousLinearEquiv :=
  (rfl)

@[simp]
theorem ofEquiv_symm [TopologicalSpace A] [IsModuleTopology A M] [IsModuleTopology A N]
    (e : ρ.toRepresentation.Equiv σ.toRepresentation) : (ofEquiv e).symm = ofEquiv e.symm :=
  (rfl)

end Iso

end Basic

section ofCharacter

variable {Γ A : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommSemiring A] [TopologicalSpace A]
  [ContinuousMul A]

/-- **The rank-one representation of a continuous character.** An element `g : Γ` acts on the
line `A` by multiplication by the unit `χ g`. -/
def ofCharacter (χ : Γ →ₜ* Aˣ) : ContinuousRep Γ A A where
  toRepresentation := Representation.ofLinearCharacter (χ : Γ →* Aˣ)
  continuous_action :=
    (((Units.continuous_val.comp χ.continuous).comp continuous_fst).mul continuous_snd).congr
      fun p => (Representation.ofLinearCharacter_apply _ p.1 p.2).symm

@[simp]
theorem ofCharacter_apply (χ : Γ →ₜ* Aˣ) (g : Γ) (a : A) : ofCharacter χ g a = χ g * a :=
  Representation.ofLinearCharacter_apply _ g a

@[simp]
theorem toRepresentation_ofCharacter (χ : Γ →ₜ* Aˣ) :
    (ofCharacter χ).toRepresentation = Representation.ofLinearCharacter (χ : Γ →* Aˣ) :=
  (rfl)

/-- The trivial character gives the trivial action on `A`. -/
theorem toRepresentation_ofCharacter_one :
    (ofCharacter (1 : Γ →ₜ* Aˣ)).toRepresentation = Representation.trivial A Γ A :=
  Representation.ofLinearCharacter_one

/-- The trivial character gives the trivial continuous representation on `A`. -/
@[simp]
theorem ofCharacter_one : ofCharacter (1 : Γ →ₜ* Aˣ) = trivial Γ A A :=
  ext fun g a => by simp

/-- **Two character lines are isomorphic exactly when the characters agree.** -/
@[simp]
theorem nonempty_iso_ofCharacter_iff (χ ψ : Γ →ₜ* Aˣ) :
    Nonempty (Iso (ofCharacter χ) (ofCharacter ψ)) ↔ χ = ψ := by
  refine ⟨fun ⟨e⟩ => ContinuousMonoidHom.ext fun g => Units.ext ?_, fun h => h ▸ ⟨.refl _⟩⟩
  -- Equivariance at `1` gives `e (χ g) = ψ g * e 1`, and linearity gives `e (ψ g) = ψ g * e 1`.
  apply EquivLike.injective e
  have hψ : e (ψ g : A) = ψ g * e 1 := by simpa using map_smul e (ψ g : A) (1 : A)
  simpa [hψ] using e.isIntertwining g 1

end ofCharacter

section BaseChange

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommSemiring A] [TopologicalSpace A]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M]

variable (B : Type*) [Ring B] [TopologicalSpace B] [IsTopologicalSemiring B] [Algebra A B]
  [ContinuousSMul A B] [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)]

/-- The base change of a jointly continuous action on a finite module is jointly continuous for
the module topology on `B ⊗[A] M`. -/
private theorem continuous_baseChange_action (ρ : ContinuousRep Γ A M) :
    Continuous fun p : Γ × (B ⊗[A] M) =>
      Representation.baseChange B ρ.toRepresentation p.1 p.2 := by
  obtain ⟨n, m, hm⟩ := Module.Finite.exists_fin (R := A) (M := M)
  have := IsModuleTopology.toContinuousAdd B (B ⊗[A] M)
  -- The coefficient-extension map `x ↦ 1 ⊗ x` is continuous, being semilinear over `A → B`.
  let ι : M →ₛₗ[algebraMap A B] B ⊗[A] M :=
    { toFun x := (1 : B) ⊗ₜ x
      map_add' := TensorProduct.tmul_add 1
      map_smul' a x := by simp [TensorProduct.tmul_smul, algebraMap_smul] }
  have hι : Continuous ι := IsModuleTopology.continuous_of_linearMapₛₗ (continuous_algebraMap A B) ι
  -- The family `1 ⊗ m i` spans `B ⊗[A] M`, and its orbits `g ↦ 1 ⊗ ρ g (m i)` are continuous.
  have hspan : Submodule.span B (Set.range fun i => (1 : B) ⊗ₜ[A] m i) = ⊤ := by
    have hrange : (Set.range fun i => (1 : B) ⊗ₜ[A] m i) =
        TensorProduct.mk A B M 1 '' Set.range m :=
      Set.range_comp (TensorProduct.mk A B M 1) m
    rw [hrange, ← Submodule.baseChange_span, hm, Submodule.baseChange_top]
  refine (IsModuleTopology.continuous_linearMap_apply_iff_of_span_eq_top
    (Representation.baseChange B ρ.toRepresentation) hspan).mpr fun i => ?_
  refine (hι.comp (ρ.continuous_orbit (m i))).congr fun g => ?_
  simp [ι, Representation.baseChange_apply]

/-- **Extension of scalars of a continuous representation** along a continuous coefficient map
`A → B`, for a finite module `M` with its module topology. The action on `B ⊗[A] M` is
`Representation.baseChange`, and `B ⊗[A] M` carries its `B`-module topology. -/
def baseChange (ρ : ContinuousRep Γ A M) : ContinuousRep Γ B (B ⊗[A] M) where
  toRepresentation := Representation.baseChange B ρ.toRepresentation
  continuous_action := continuous_baseChange_action B ρ

@[simp]
theorem toRepresentation_baseChange (ρ : ContinuousRep Γ A M) :
    (ρ.baseChange B).toRepresentation = Representation.baseChange B ρ.toRepresentation :=
  (rfl)

/-- The base-changed action is the base change of the original operators. -/
@[simp]
theorem baseChange_apply (ρ : ContinuousRep Γ A M) (g : Γ) :
    ρ.baseChange B g = (ρ g).baseChange B :=
  Representation.baseChange_apply ρ.toRepresentation g

section Iso

variable {N : Type*} [AddCommMonoid N] [Module A N] [TopologicalSpace N] [IsModuleTopology A N]
  [Module.Finite A N] [TopologicalSpace (B ⊗[A] N)] [IsModuleTopology B (B ⊗[A] N)]
  {ρ : ContinuousRep Γ A M} {σ : ContinuousRep Γ A N}

/-- Extension of scalars of an isomorphism of continuous representations. -/
def Iso.baseChange (e : Iso ρ σ) : Iso (ρ.baseChange B) (σ.baseChange B) :=
  .ofEquiv (e.toRepresentationEquiv.baseChange B)

@[simp]
theorem Iso.baseChange_tmul (e : Iso ρ σ) (b : B) (x : M) :
    e.baseChange B (b ⊗ₜ x) = b ⊗ₜ e x :=
  Representation.Equiv.baseChange_tmul _ B b x

end Iso

variable (Γ A M) in
/-- **Extension of scalars of the trivial representation is trivial**, through the identity of
`B ⊗[A] M`. -/
def baseChangeTrivialIso : Iso ((trivial Γ A M).baseChange B) (trivial Γ B (B ⊗[A] M)) :=
  .ofEquiv (.mk (.refl _ _) fun g => by ext; simp)

@[simp]
theorem baseChangeTrivialIso_apply (x : B ⊗[A] M) : baseChangeTrivialIso Γ A M B x = x :=
  (rfl)

@[simp]
theorem baseChangeTrivialIso_symm_apply (x : B ⊗[A] M) :
    (baseChangeTrivialIso Γ A M B).symm x = x :=
  (rfl)

end BaseChange

section BaseChangeSelf

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]
  [IsTopologicalSemiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [IsModuleTopology A M] [Module.Finite A M] [TopologicalSpace (A ⊗[A] M)]
  [IsModuleTopology A (A ⊗[A] M)]

/-- **Extension of scalars to the coefficient ring itself is trivial**: `A ⊗[A] M ≅ M` through
`TensorProduct.lid`, equivariantly and homeomorphically. -/
def baseChangeSelfIso (ρ : ContinuousRep Γ A M) : Iso (ρ.baseChange A) ρ :=
  .ofEquiv (.mk (TensorProduct.lid A M) fun g => by ext; simp)

@[simp]
theorem baseChangeSelfIso_tmul (ρ : ContinuousRep Γ A M) (a : A) (x : M) :
    ρ.baseChangeSelfIso (a ⊗ₜ x) = a • x :=
  TensorProduct.lid_tmul x a

@[simp]
theorem baseChangeSelfIso_symm_apply (ρ : ContinuousRep Γ A M) (x : M) :
    ρ.baseChangeSelfIso.symm x = 1 ⊗ₜ x :=
  TensorProduct.lid_symm_apply x

end BaseChangeSelf

section BaseChangeTrans

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommSemiring A] [TopologicalSpace A]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M]

variable (B C : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalSemiring B] [Algebra A B]
  [ContinuousSMul A B] [Ring C] [TopologicalSpace C] [IsTopologicalSemiring C] [Algebra A C]
  [Algebra B C] [IsScalarTower A B C] [ContinuousSMul A C] [ContinuousSMul B C]
  [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)]
  [TopologicalSpace (C ⊗[A] M)] [IsModuleTopology C (C ⊗[A] M)]
  [TopologicalSpace (C ⊗[B] (B ⊗[A] M))] [IsModuleTopology C (C ⊗[B] (B ⊗[A] M))]

/-- **Extension of scalars in stages**: for `A → B → C`, extending to `B` and then to `C` is
extending to `C`, through `TensorProduct.AlgebraTensorModule.cancelBaseChange`, which sends
`c ⊗ (b ⊗ x)` to `(b • c) ⊗ x`. -/
def baseChangeTransIso (ρ : ContinuousRep Γ A M) :
    Iso ((ρ.baseChange B).baseChange C) (ρ.baseChange C) :=
  .ofEquiv (.mk (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C M) fun g => by
    ext; simp)

@[simp]
theorem baseChangeTransIso_tmul (ρ : ContinuousRep Γ A M) (c : C) (b : B) (x : M) :
    ρ.baseChangeTransIso B C (c ⊗ₜ (b ⊗ₜ x)) = (b • c) ⊗ₜ x :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul A B C c x b

@[simp]
theorem baseChangeTransIso_symm_tmul (ρ : ContinuousRep Γ A M) (c : C) (x : M) :
    (ρ.baseChangeTransIso B C).symm (c ⊗ₜ x) = c ⊗ₜ (1 ⊗ₜ x) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul A B C c x

end BaseChangeTrans

section BaseChangeTransTrans

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommSemiring A] [TopologicalSpace A]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M]

variable (B C D : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalSemiring B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalSemiring C]
  [Ring D] [TopologicalSpace D] [IsTopologicalSemiring D]
  [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B C] [Algebra B D] [Algebra C D]
  [IsScalarTower A B C] [IsScalarTower A B D] [IsScalarTower A C D] [IsScalarTower B C D]
  [ContinuousSMul A B] [ContinuousSMul A C] [ContinuousSMul A D] [ContinuousSMul B C]
  [ContinuousSMul B D] [ContinuousSMul C D]
  [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)]
  [TopologicalSpace (C ⊗[A] M)] [IsModuleTopology C (C ⊗[A] M)]
  [TopologicalSpace (D ⊗[A] M)] [IsModuleTopology D (D ⊗[A] M)]
  [TopologicalSpace (C ⊗[B] (B ⊗[A] M))] [IsModuleTopology C (C ⊗[B] (B ⊗[A] M))]
  [TopologicalSpace (D ⊗[B] (B ⊗[A] M))] [IsModuleTopology D (D ⊗[B] (B ⊗[A] M))]
  [TopologicalSpace (D ⊗[C] (C ⊗[A] M))] [IsModuleTopology D (D ⊗[C] (C ⊗[A] M))]
  [TopologicalSpace (D ⊗[C] (C ⊗[B] (B ⊗[A] M)))]
  [IsModuleTopology D (D ⊗[C] (C ⊗[B] (B ⊗[A] M)))]

/-- **Extension of scalars in three stages is coherent**: for `A → B → C → D`, the two ways of
collapsing `D ⊗[C] (C ⊗[B] (B ⊗[A] M))` to `D ⊗[A] M` by `baseChangeTransIso` agree. -/
theorem baseChangeTransIso_trans_baseChangeTransIso (ρ : ContinuousRep Γ A M) :
    ((ρ.baseChange B).baseChangeTransIso C D).trans (ρ.baseChangeTransIso B D) =
      ((ρ.baseChangeTransIso B C).baseChange D).trans (ρ.baseChangeTransIso C D) := by
  ext x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp_all
  | tmul d y =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp_all [TensorProduct.tmul_add]
    | tmul c z =>
      induction z using TensorProduct.inductionOn with
      | add z w hz hw => simp_all [TensorProduct.tmul_add]
      | tmul b x => simp [smul_assoc]

end BaseChangeTransTrans

section BaseChangeOfCharacter

variable {Γ A : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommSemiring A] [TopologicalSpace A]
  [IsTopologicalSemiring A]

variable (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalSemiring B] [Algebra A B]
  [ContinuousSMul A B] [TopologicalSpace (B ⊗[A] A)] [IsModuleTopology B (B ⊗[A] A)]

/-- **Extension of scalars of a character line is the line of the extended character**: the
base change of `ofCharacter χ` to `B` is the line `B` on which `g` acts by the image of `χ g`
in `Bˣ`, through `TensorProduct.AlgebraTensorModule.rid`. -/
def baseChangeOfCharacterIso (χ : Γ →ₜ* Aˣ) :
    Iso ((ofCharacter χ).baseChange B)
      (ofCharacter ((ContinuousMonoidHom.unitsMap
        ⟨(algebraMap A B : A →* B), continuous_algebraMap A B⟩).comp χ)) :=
  .ofEquiv (.mk (TensorProduct.AlgebraTensorModule.rid A B B) fun g => by
    -- The extended character takes the value `algebraMap A B (χ g)` at `g`.
    have hχ : ((ContinuousMonoidHom.unitsMap
        ⟨(algebraMap A B : A →* B), continuous_algebraMap A B⟩).comp χ g : B) =
        algebraMap A B (χ g) :=
      ContinuousMonoidHom.coe_unitsMap_apply _ _
    ext
    simpa [Algebra.smul_def] using hχ.symm)

@[simp]
theorem baseChangeOfCharacterIso_tmul (χ : Γ →ₜ* Aˣ) (b : B) (a : A) :
    baseChangeOfCharacterIso B χ (b ⊗ₜ a) = a • b :=
  TensorProduct.AlgebraTensorModule.rid_tmul B a b

end BaseChangeOfCharacter

section Dual

variable {Γ A M : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Finite A M] [Module.Projective A M]
  [TopologicalSpace (Module.Dual A M)] [IsModuleTopology A (Module.Dual A M)]

/-- The contragredient action on the dual of a finite projective module is jointly continuous
for the module topology on `Module.Dual A M`. -/
private theorem continuous_dual_action (ρ : ContinuousRep Γ A M) :
    Continuous fun p : Γ × Module.Dual A M => ρ.toRepresentation.dual p.1 p.2 := by
  -- A finite dual basis `x = ∑ j, φ j x • b j` writes every functional `ψ` as
  -- `∑ j, ψ (b j) • φ j`, and the coefficients of `ψ ∘ ρ g⁻¹` are continuous in `(g, ψ)`.
  obtain ⟨n, b, φ, hb⟩ := exists_sum_dual_smul_eq (R := A) (M := M)
  have := IsModuleTopology.toContinuousAdd A (Module.Dual A M)
  have := IsModuleTopology.toContinuousSMul A (Module.Dual A M)
  have hev : Continuous fun p : Module.Dual A M × M => p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_right (LinearMap.id : Module.Dual A M →ₗ[A] _)
  have h : Continuous fun p : Γ × Module.Dual A M => ∑ j, p.2 (ρ p.1⁻¹ (b j)) • φ j :=
    continuous_finsetSum _ fun j _ ↦ (hev.comp (continuous_snd.prodMk
      ((ρ.continuous_orbit (b j)).comp continuous_fst.inv))).smul continuous_const
  refine h.congr fun p ↦ LinearMap.ext fun x ↦ ?_
  conv_rhs => rw [← hb x]
  simp [Module.Dual.transpose_apply, mul_comm]

/-- **The contragredient representation** of a continuous representation on a finite projective
module: `Γ` acts on `Module.Dual A M` by `g • ψ = ψ ∘ ρ g⁻¹`, jointly continuously for the module
topology on the dual. -/
def dual (ρ : ContinuousRep Γ A M) : ContinuousRep Γ A (Module.Dual A M) where
  toRepresentation := ρ.toRepresentation.dual
  continuous_action := continuous_dual_action ρ

@[simp]
theorem toRepresentation_dual (ρ : ContinuousRep Γ A M) :
    ρ.dual.toRepresentation = ρ.toRepresentation.dual :=
  (rfl)

/-- The contragredient action is the transpose of the inverse action. -/
theorem dual_apply (ρ : ContinuousRep Γ A M) (g : Γ) :
    ρ.dual g = Module.Dual.transpose (R := A) (ρ g⁻¹) :=
  (rfl)

/-- The contragredient action evaluated at a vector. -/
@[simp]
theorem dual_apply_apply (ρ : ContinuousRep Γ A M) (g : Γ) (ψ : Module.Dual A M) (x : M) :
    ρ.dual g ψ x = ψ (ρ g⁻¹ x) :=
  (rfl)

end Dual

end ContinuousRep

end TauCeti
