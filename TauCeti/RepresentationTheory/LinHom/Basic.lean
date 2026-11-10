/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.RepresentationTheory.OfModule
import TauCeti.RepresentationTheory.Regular

/-!
# Projectivity of the conjugation Hom representation

Let `k` be a commutative semiring, `G` a finite group, `ρ` a representation of `G` on `V` and `σ`
a representation of `G` on `W`. The `k`-linear maps `V → W` carry the conjugation action
`g • φ = σ g ∘ φ ∘ ρ g⁻¹` (Mathlib's `Representation.linHom`). This file proves that when
`ρ.asModule` is a finitely generated projective `k[G]`-module and `W` is projective over `k`, the
conjugation module `Hom_k(V, W)` is a projective `k[G]`-module. It also records that `Hom_k(V, W)`
is a finitely generated `k[G]`-module whenever `V` is finitely generated and projective and `W` is
finitely generated over `k`.

For the regular representation the conjugation module is induced: `Hom_k(k[G], W)` is identified
with `k[G]^* ⊗ W` by the contraction map, the dual of `k[G]` with `k[G]` by the coefficient
pairing (`Representation.dualLeftRegularEquiv`), and the diagonal action on `k[G] ⊗ W` with the
action on the first factor alone (`Representation.leftRegularTensorEquivTrivial`). This exhibits
`Hom_k(k[G], W)` as the base change `k[G] ⊗[k] W`. A finitely generated projective `k[G]`-module
is a direct summand of some `k[G]ⁿ`, and precomposition with the inclusion and projection makes
`Hom_k(V, W)` a direct summand of `Hom_k(k[G], W)ⁿ`.

Over a field `k` of characteristic `p` this says that `Hom_k(P, S)` is a projective `k[G]`-module
for every finitely generated projective `k[G]`-module `P` and every `k[G]`-module `S`. In Brauer's
theory of modular characters this is what lets `Hom_{k[G]}(P, S) = Hom_k(P, S)^G` be studied
through the invariants of a projective module, whose dimension is computed by characters after
lifting to characteristic zero.

## Main results

* `Representation.Equiv.dualTensorHomOfProjective`: for `V` finitely generated and projective
  over `k`, the contraction `V^* ⊗ W ≃ Hom_k(V, W)` is an equivalence of representations.
* `Representation.nonempty_linHom_leftRegular_asModule_linearEquiv`: the conjugation module
  `Hom_k(k[G], W)` is isomorphic to `k[G] ⊗[k] W`.
* `Representation.instProjectiveAsModuleLinHom`: `Hom_k(V, W)` is a projective `k[G]`-module.
* `Representation.instFiniteAsModuleLinHom`: `Hom_k(V, W)` is a finitely generated
  `k[G]`-module when `V` is finite projective and `W` is finite over `k`.
* `Representation.natCard_linearMap_eq_natCard_invariants_linHom`: the `k[G]`-linear maps `M → S`
  are counted by the invariants of the conjugation representation on `Hom_k(M, S)`.
* `Representation.Equiv.linHomComp`: an isomorphism `ρ.comp f ≅ ρ'.comp f` of representations
  restricted along a group homomorphism `f : H →* G` induces an isomorphism of the restricted
  conjugation representations `Hom_k(ρ, σ) ≅ Hom_k(ρ', σ)`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
* R. G. Swan, *Induced representations and projective modules*, Ann. of Math. 71 (1960).
-/

public section

open scoped MonoidAlgebra TensorProduct

noncomputable section

namespace Representation

universe u v w w'

variable {k : Type u} [CommSemiring k] {G : Type v} [Group G]
  {V : Type w} [AddCommMonoid V] [Module k V] {W : Type w'} [AddCommMonoid W] [Module k W]

namespace Equiv

/-- **The contraction `V^* ⊗ W ≃ Hom_k(V, W)` as an equivalence of representations**, for `V`
finitely generated and projective over the commutative semiring `k`. It intertwines the tensor
product of the dual of `ρ` with `σ` and the conjugation representation `linHom ρ σ`. This
generalizes Mathlib's `Representation.Equiv.dualTensorHom`, which is stated for
finite-dimensional vector spaces over a field. -/
def dualTensorHomOfProjective [Module.Finite k V] [Module.Projective k V]
    (ρ : Representation k G V) (σ : Representation k G W) :
    (ρ.dual.tprod σ).Equiv (linHom ρ σ) :=
  .mk (dualTensorHomEquiv k V W) (dualTensorHom_comm ρ σ)

@[simp]
theorem dualTensorHomOfProjective_apply [Module.Finite k V] [Module.Projective k V]
    (ρ : Representation k G V) (σ : Representation k G W) (x : Module.Dual k V ⊗[k] W) :
    dualTensorHomOfProjective ρ σ x = _root_.dualTensorHom k V W x :=
  (rfl)

end Equiv

variable (σ : Representation k G W)

/-- **The coinduced module `Hom_k(k[G], W)` is the induced module `k[G] ⊗[k] W`.** For a finite
group `G` and any representation `σ` of `G` on `W`, the conjugation module of `k`-linear maps from
the regular representation to `σ` is isomorphic to the base change `k[G] ⊗[k] W`, on which `k[G]`
acts on the first factor. -/
theorem nonempty_linHom_leftRegular_asModule_linearEquiv [Finite G] :
    Nonempty ((linHom (leftRegular k G) σ).asModule ≃ₗ[k[G]] k[G] ⊗[k] W) := by
  -- Pass through `k[G]^* ⊗ W`, `k[G] ⊗ W` with the diagonal action, and `k[G] ⊗ W` with the
  -- action on the first factor, which is the representation underlying `k[G] ⊗[k] W`.
  let e₁ : (leftRegular k G).dual.Equiv (leftRegular k G) := dualLeftRegularEquiv
  let e₂ : ((leftRegular k G).dual.tprod σ).Equiv ((leftRegular k G).tprod σ) :=
    .mk (TensorProduct.congr e₁.toLinearEquiv (LinearEquiv.refl k W)) fun g ↦ by
      ext f w
      simpa using congrArg (· ⊗ₜ[k] σ g w)
        (IntertwiningMap.isIntertwining _ _ e₁.toIntertwiningMap g f)
  let e₃ : ((leftRegular k G).tprod (trivial k G W)).Equiv (ofModule' (k[G] ⊗[k] W)) :=
    .mk (LinearEquiv.refl k _) fun g ↦ by
      ext a w
      simp [TauCeti.Representation.ofModule'_apply, TensorProduct.smul_tmul']
  exact ⟨(TauCeti.Representation.asModuleLinearEquivOfEquiv
    ((((Equiv.dualTensorHomOfProjective _ σ).symm.trans e₂).trans
      (leftRegularTensorEquivTrivial σ)).trans e₃)).trans
    (TauCeti.Representation.ofModule'AsModuleEquiv _)⟩

variable (ρ : Representation k G V)

/-- When `ρ.asModule` is a direct summand of `k[G]ⁿ`, precomposition with the inclusion and the
projection exhibits the conjugation module `Hom_k(V, W)` as a direct summand of
`Hom_k(k[G], W)ⁿ`. -/
private theorem exists_comp_eq_id_linHom [Module.Finite k[G] ρ.asModule]
    [Module.Projective k[G] ρ.asModule] :
    ∃ (n : ℕ)
      (i : (linHom ρ σ).asModule →ₗ[k[G]] Fin n → (linHom (leftRegular k G) σ).asModule)
      (s : (Fin n → (linHom (leftRegular k G) σ).asModule) →ₗ[k[G]] (linHom ρ σ).asModule),
      s ∘ₗ i = LinearMap.id := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective k[G] ρ.asModule
  let E : (leftRegular k G).asModule ≃ₗ[k[G]] k[G] := ofMulActionSelfAsModuleEquiv
  let a (j : Fin n) : IntertwiningMap (leftRegular k G) ρ :=
    (IntertwiningMap.equivLinearMapAsModule _ _).symm
      (f ∘ₗ LinearMap.single k[G] (fun _ ↦ k[G]) j ∘ₗ E.toLinearMap)
  let b (j : Fin n) : IntertwiningMap ρ (leftRegular k G) :=
    (IntertwiningMap.equivLinearMapAsModule _ _).symm
      (E.symm.toLinearMap ∘ₗ LinearMap.proj j ∘ₗ g)
  refine ⟨n, LinearMap.pi fun j ↦
      IntertwiningMap.equivLinearMapAsModule _ _ ((a j).lcomp σ),
    ∑ j, IntertwiningMap.equivLinearMapAsModule _ _ ((b j).lcomp σ) ∘ₗ
      LinearMap.proj j, ?_⟩
  -- On the underlying types, `a j = f ∘ single j` and `b j = proj j ∘ g`. The type synonym
  -- `ρ.asModule` keeps `simp` from rewriting with `equivLinearMapAsModule_symm_apply`, so these
  -- unfoldings are recorded by `rfl`.
  have hab (v : V) : ∑ j, a j (b j v) = v := by
    have ha (j : Fin n) (y : k[G]) : a j y = ρ.asModuleEquiv (f (Pi.single j y)) := rfl
    have hb (j : Fin n) : b j v = g (ρ.asModuleEquiv.symm v) j := rfl
    simp only [ha, hb]
    rw [← map_sum, ← map_sum, Finset.univ_sum_single, ← LinearMap.comp_apply, hfg,
      LinearMap.id_apply, LinearEquiv.apply_symm_apply]
  ext φ : 1
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.pi_apply,
    LinearMap.coe_proj, Function.eval, IntertwiningMap.equivLinearMapAsModule_apply,
    LinearMap.id_apply]
  have key (φ : V →ₗ[k] W) :
      ∑ j, (b j).lcomp σ ((a j).lcomp σ φ) = φ := by
    ext v
    simp [← map_sum, hab]
  -- The goal is `key φ`, read in the type synonym `(linHom ρ σ).asModule` of `V →ₗ[k] W`.
  exact key φ

/-- If `V` is finitely generated and projective over `k` and `W` is finitely generated over `k`,
then the conjugation module `Hom_k(V, W)` is a finitely generated `k[G]`-module. -/
instance instFiniteAsModuleLinHom [Module.Finite k V] [Module.Projective k V] [Module.Finite k W] :
    Module.Finite k[G] (linHom ρ σ).asModule :=
  have : Module.Finite k (V →ₗ[k] W) := .equiv (dualTensorHomEquiv k V W)
  .of_restrictScalars_finite k k[G] _

variable [Finite G]

/-- **The conjugation module of a projective module is projective.** For a finite group `G`, if
`ρ.asModule` is a finitely generated projective `k[G]`-module and `W` is projective over `k`, then
the conjugation module `Hom_k(V, W)` is a projective `k[G]`-module. -/
instance instProjectiveAsModuleLinHom [Module.Finite k[G] ρ.asModule]
    [Module.Projective k[G] ρ.asModule] [Module.Projective k W] :
    Module.Projective k[G] (linHom ρ σ).asModule := by
  obtain ⟨n, i, s, h⟩ := exists_comp_eq_id_linHom σ ρ
  obtain ⟨e⟩ := nonempty_linHom_leftRegular_asModule_linearEquiv (k := k) σ
  have : Module.Projective k[G] (linHom (leftRegular k G) σ).asModule := .of_equiv' e.symm
  have : Module.Projective k[G] (Fin n → (linHom (leftRegular k G) σ).asModule) :=
    .of_equiv' DFinsupp.linearEquivFunOnFintype
  exact .of_split i s h

section Invariants

/-- The `k[G]`-linear maps `M → S` are counted by the invariants of the conjugation
representation on `Hom_k(M, S)`. -/
theorem natCard_linearMap_eq_natCard_invariants_linHom {k : Type*} [CommRing k] {G : Type*}
    [Group G] (M S : Type*) [AddCommGroup M] [Module k M] [Module k[G] M]
    [IsScalarTower k k[G] M] [AddCommGroup S] [Module k S] [Module k[G] S]
    [IsScalarTower k k[G] S] :
    Nat.card (M →ₗ[k[G]] S) = Nat.card (Representation.invariants (linHom
      (Representation.ofModule' (k := k) (G := G) M)
      (Representation.ofModule' (k := k) (G := G) S))) :=
  let ρ := Representation.ofModule' (k := k) (G := G) M
  let σ := Representation.ofModule' (k := k) (G := G) S
  (Nat.card_congr (((Representation.invariantsEquivIntertwiningMap ρ σ).trans
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ)).toAddEquiv.trans
      ((TauCeti.Representation.ofModule'AsModuleEquiv (k := k) (G := G) M).arrowCongrAddEquiv
        (TauCeti.Representation.ofModule'AsModuleEquiv (k := k) (G := G) S))).toEquiv).symm

/-- **Functoriality of the conjugation representation in an equivariant isomorphism.** An
isomorphism `e : ρ.comp f ≅ ρ'.comp f` of representations restricted along `f : H →* G` induces
the isomorphism `φ ↦ φ ∘ e.symm` between the conjugation representations `Hom_k(ρ, σ)` and
`Hom_k(ρ', σ)` restricted along `f`. -/
def Equiv.linHomComp {k : Type*} [CommRing k] {G H : Type*} [Group G] [Group H]
    {V V' W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    [AddCommGroup W] [Module k W] {ρ : Representation k G V} {ρ' : Representation k G V'}
    {f : H →* G} (e : Representation.Equiv (ρ.comp f) (ρ'.comp f)) (σ : Representation k G W) :
    Representation.Equiv ((linHom ρ σ).comp f) ((linHom ρ' σ).comp f) :=
  .mk (LinearEquiv.congrLeft W k e.toLinearEquiv) fun h ↦ by
    ext φ x
    simp only [LinearMap.comp_apply, MonoidHom.comp_apply, linHom_apply,
      LinearEquiv.congrLeft_apply, Equiv.toFun_as_coe, LinearEquiv.coe_coe, ← map_inv]
    exact congrArg (σ (f h)) (congrArg φ (e.symm.isIntertwining _ _ h⁻¹ x).symm)

@[simp]
theorem Equiv.linHomComp_apply {k : Type*} [CommRing k] {G H : Type*} [Group G] [Group H]
    {V V' W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    [AddCommGroup W] [Module k W] {ρ : Representation k G V} {ρ' : Representation k G V'}
    {f : H →* G} (e : Representation.Equiv (ρ.comp f) (ρ'.comp f)) (σ : Representation k G W)
    (φ : V →ₗ[k] W) (x : V') :
    e.linHomComp σ φ x = φ (e.symm x) :=
  (rfl)

end Invariants

end Representation
