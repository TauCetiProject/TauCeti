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
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.LinearCharacter.Basic

/-!
# Jointly continuous representations

A *continuous representation* of a topological monoid `Γ` on a topological `A`-module `M`, in the
sense used for Galois representations, is a linear representation `Γ →* End_A M` whose action map
`Γ × M → M` is jointly continuous. This is stronger than asking each operator to be continuous,
which is what Mathlib's `ContRepresentation` records: for instance the multiplication action of
`ℤ_ℓˣ` on `ℚ_ℓ` with the discrete topology has continuous operators but is not jointly
continuous. This file packages such an action as `TauCeti.ContinuousRep Γ A M` and develops the
elementary operations needed to build integral models of `ℓ`-adic representations: isomorphisms,
the line attached to a continuous character, and extension of scalars.

The typical module is a finite module `M` over a topological ring `A`, carrying its module
topology (`IsModuleTopology A M`). Over such modules every linear map is continuous, so an
equivariant linear equivalence is automatically an isomorphism of continuous representations
(`TauCeti.ContinuousRep.Iso.ofEquiv`). Extension of scalars along a continuous ring map `A → B`
gives `B ⊗[A] M` its `B`-module topology; the base-changed action is again jointly continuous
because a finite generating family of `M` presents `B ⊗[A] M` as an open quotient of `Bⁿ`,
on which the action is an explicit continuous formula.

## Main definitions

* `TauCeti.ContinuousRep Γ A M`: a representation of `Γ` on `M` whose action is jointly
  continuous.
* `TauCeti.ContinuousRep.toContRepresentation`: the underlying Mathlib `ContRepresentation`.
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

## Main results

* `TauCeti.ContinuousRep.continuous_apply`: each operator of a continuous representation is
  continuous.
* `TauCeti.ContinuousRep.nonempty_iso_ofCharacter_iff`: two character lines are isomorphic
  exactly when the characters agree.
* `TauCeti.ContinuousRep.baseChangeTransIso_trans_baseChangeTransIso`: the two identifications
  of a threefold scalar extension `A → B → C → D` with the extension along `A → D` agree.

## Implementation notes

The topology on a base change `B ⊗[A] M` is an instance argument together with
`IsModuleTopology B (B ⊗[A] M)`, as for any module topology in Mathlib, so a consumer may supply
`moduleTopology B (B ⊗[A] M)` or any topology known to coincide with it. Only finiteness of `M`
is needed for the base-changed action to be continuous; projectivity plays no role here.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- **A jointly continuous representation.** A linear representation of the topological monoid
`Γ` on the topological `A`-module `M` whose action map `Γ × M → M` is continuous. -/
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

/-- **Each operator of a jointly continuous representation is continuous.** -/
@[fun_prop]
theorem continuous_apply (ρ : ContinuousRep Γ A M) (g : Γ) : Continuous (ρ g) :=
  ρ.continuous_action.comp (continuous_const.prodMk continuous_id)

/-- The orbit map `g ↦ ρ g x` of a jointly continuous representation is continuous. -/
@[fun_prop]
theorem continuous_orbit (ρ : ContinuousRep Γ A M) (x : M) : Continuous fun g => ρ g x :=
  ρ.continuous_action.comp (continuous_id.prodMk continuous_const)

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

end ContRepresentation

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

/-- **Two character lines are isomorphic exactly when the characters agree.** An isomorphism `e`
of lines is multiplication by `e 1`, so equivariance at `1` reads `e (χ g) = e (ψ g)`. -/
@[simp]
theorem nonempty_iso_ofCharacter_iff (χ ψ : Γ →ₜ* Aˣ) :
    Nonempty (Iso (ofCharacter χ) (ofCharacter ψ)) ↔ χ = ψ := by
  refine ⟨fun ⟨e⟩ => ContinuousMonoidHom.ext fun g => Units.ext ?_, fun h => h ▸ ⟨.refl _⟩⟩
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
the module topology on `B ⊗[A] M`. A finite generating family `m` of `M` presents `B ⊗[A] M` as
the open quotient `b ↦ ∑ i, b i • (1 ⊗ m i)` of `Bⁿ`, and through that quotient the action is
`(g, b) ↦ ∑ i, b i • (1 ⊗ ρ g (m i))`. -/
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
  -- The presentation of `B ⊗[A] M` as an open quotient of `Bⁿ`.
  let q := Fintype.linearCombination B fun i => (1 : B) ⊗ₜ[A] m i
  have hq : IsOpenQuotientMap q := by
    refine IsModuleTopology.isOpenQuotientMap_of_surjective (LinearMap.range_eq_top.mp ?_)
    have hrange : (Set.range fun i => (1 : B) ⊗ₜ[A] m i) =
        TensorProduct.mk A B M 1 '' Set.range m :=
      Set.range_comp (TensorProduct.mk A B M 1) m
    rw [Fintype.range_linearCombination, hrange, ← Submodule.baseChange_span, hm,
      Submodule.baseChange_top]
  refine ((IsOpenQuotientMap.id.prodMap hq).continuous_comp_iff).mp ?_
  have hF : Continuous fun p : Γ × (Fin n → B) => ∑ i, p.2 i • ι (ρ p.1 (m i)) := by
    fun_prop
  refine hF.congr fun p => ?_
  simp [q, ι, Fintype.linearCombination_apply, Representation.baseChange_apply]

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
      (ofCharacter (ContinuousMonoidHom.comp
        ⟨Units.map (algebraMap A B : A →* B), Continuous.units_map _ (continuous_algebraMap A B)⟩
        χ)) :=
  .ofEquiv (.mk (TensorProduct.AlgebraTensorModule.rid A B B) fun g => by
    -- The extended character takes the value `algebraMap A B (χ g)` at `g`.
    have hχ : (ContinuousMonoidHom.comp
        ⟨Units.map (algebraMap A B : A →* B), Continuous.units_map _ (continuous_algebraMap A B)⟩
        χ g : B) = algebraMap A B (χ g) :=
      Units.coe_map _ _
    ext
    simpa [Algebra.smul_def] using hχ.symm)

@[simp]
theorem baseChangeOfCharacterIso_tmul (χ : Γ →ₜ* Aˣ) (b : B) (a : A) :
    baseChangeOfCharacterIso B χ (b ⊗ₜ a) = a • b :=
  TensorProduct.AlgebraTensorModule.rid_tmul B a b

end BaseChangeOfCharacter

end ContinuousRep

end TauCeti
