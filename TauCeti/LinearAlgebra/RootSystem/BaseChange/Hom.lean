/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Basic
public import TauCeti.LinearAlgebra.RootSystem.Flip
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Extension of scalars of root-pairing morphisms and automorphisms

Let `P` and `Q` be root pairings over a commutative ring `R` with finite free coweight spaces, and
let `S` be a faithful `R`-algebra. Extending the weight and coweight maps by `S ⊗[R] -` while
keeping the same bijection of root indices lifts every morphism `f : P.Hom Q` to a morphism
`f.baseChange S : (P.baseChange S).Hom (Q.baseChange S)`, and every equivalence `e : P.Equiv Q` to
an equivalence `e.baseChange S : (P.baseChange S).Equiv (Q.baseChange S)`.

On automorphisms this gives an injective group homomorphism
`RootPairing.autBaseChangeHom P S : P.Aut →* (P.baseChange S).Aut` that commutes with root
reflections and identifies the Weyl group of `P` with the Weyl group of `P.baseChange S`, with no
spanning, finiteness, or reducedness hypothesis on the roots.

This file also packages the covariant linear action `g ↦ g.coweightEquiv.symm` of `P.Aut` on the
coweight module as `RootPairing.Equiv.forwardCoweightHom : P.Aut →* (N ≃ₗ[R] N)`, obtained by
composing `RootPairing.Equiv.autFlip` with the weight-space representation of `P.flip`.

## Main definitions

* `RootPairing.Equiv.forwardCoweightHom`: the covariant coweight-space representation
  `P.Aut →* (N ≃ₗ[R] N)`, sending `g` to `g.coweightEquiv.symm`.
* `RootPairing.Hom.baseChange` and `RootPairing.Equiv.baseChange`: scalar extension of morphisms
  and equivalences of root pairings along a faithful algebra.
* `RootPairing.autBaseChangeHom`: scalar extension of automorphisms as an injective group
  homomorphism `P.Aut →* (P.baseChange S).Aut`.
* `RootPairing.weylGroupBaseChangeMulEquiv`: the induced group isomorphism
  `P.weylGroup ≃* (P.baseChange S).weylGroup`.

## Main results

* `RootPairing.Hom.ext_weightMap`: a morphism of root pairings is determined by its weight map.
* `RootPairing.Hom.baseChange_injective`, `RootPairing.Equiv.baseChange_injective`, and
  `RootPairing.autBaseChangeHom_injective`: scalar extension along a faithful algebra is injective
  on morphisms, equivalences, and automorphisms.
* `RootPairing.weylGroup_map_autBaseChangeHom` and
  `RootPairing.autBaseChangeHom_mem_weylGroup_iff`: scalar extension maps `P.weylGroup` onto
  `(P.baseChange S).weylGroup` and reflects membership in the Weyl group.

## References

* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §6.1 and §6.7.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

open Function Module Set TensorProduct

namespace RootPairing

section General

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]

namespace Hom

/-- A morphism of root pairings is determined by its linear map on weight spaces: the coweight map
is determined through the perfect pairing, and the index bijection through injectivity of `Q.root`.
This generalizes `RootPairing.Hom.weightHom_injective` from endomorphisms to arbitrary morphisms. -/
theorem ext_weightMap {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}
    {f g : P.Hom Q} (h : f.weightMap = g.weightMap) : f = g := by
  ext x
  · exact congr($h x)
  · refine P.flip.toPerfPair.injective ?_
    rw [← f.weight_coweight_transpose_apply, ← g.weight_coweight_transpose_apply, h]
  · refine Q.root.injective ?_
    rw [← f.root_weightMap_apply, ← g.root_weightMap_apply, h]

end Hom

namespace Equiv

/-- The covariant linear representation of `P.Aut` on the coweight space `N`, sending an
automorphism `g` to the contragredient `g.coweightEquiv.symm` of its action on weights. It is the
weight-space representation of `P.flip` pulled back along `RootPairing.Equiv.autFlip`. -/
noncomputable def forwardCoweightHom (P : RootPairing ι R M N) : P.Aut →* (N ≃ₗ[R] N) :=
  (weightHom P.flip).comp (autFlip P).toMonoidHom

/-- `RootPairing.Equiv.forwardCoweightHom` sends an automorphism `g` to `g.coweightEquiv.symm`. -/
@[simp]
theorem forwardCoweightHom_apply {P : RootPairing ι R M N} (g : P.Aut) :
    forwardCoweightHom P g = g.coweightEquiv.symm :=
  weightEquiv_autFlip g

/-- An automorphism of a root pairing is determined by its forward action on coweights. -/
theorem forwardCoweightHom_injective (P : RootPairing ι R M N) :
    Injective (forwardCoweightHom P) :=
  (weightHom_injective P.flip).comp (autFlip P).injective

/-- The forward coweight action of a root reflection is the corresponding coreflection. -/
theorem forwardCoweightHom_reflection (P : RootPairing ι R M N) (i : ι) :
    forwardCoweightHom P (reflection P i) = P.coreflection i := by
  ext y
  rw [forwardCoweightHom_apply, LinearEquiv.symm_apply_eq, reflection_coweightEquiv,
    coreflection_same]

end Equiv

end General

section BaseChange

variable {ι ι₂ ι₃ R M N M₂ N₂ M₃ N₃ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃]
  (S : Type*) [CommRing S] [Algebra R S] [FaithfulSMul R S]

namespace Hom

variable {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} {T : RootPairing ι₃ R M₃ N₃}
  [Free R N] [Module.Finite R N] [Free R N₂] [Module.Finite R N₂]

/-- **Extension of scalars of a morphism of root pairings.** The weight and coweight maps are
extended `S`-linearly to `S ⊗[R] -`, and the root-index bijection is unchanged. -/
noncomputable def baseChange (f : P.Hom Q) : (P.baseChange S).Hom (Q.baseChange S) where
  weightMap := f.weightMap.baseChange S
  coweightMap := f.coweightMap.baseChange S
  indexEquiv := f.indexEquiv
  weight_coweight_transpose := by
    refine TensorProduct.AlgebraTensorModule.ext fun b n₂ ↦ ?_
    refine TensorProduct.AlgebraTensorModule.ext fun a m ↦ ?_
    have h := congr($(f.weight_coweight_transpose_apply P Q n₂) m)
    simpa only [LinearMap.comp_apply, LinearMap.dualMap_apply, flip_toLinearMap,
      LinearEquiv.coe_coe, LinearMap.toPerfPair_apply, LinearMap.flip_apply,
      baseChange_toLinearMap, LinearMap.baseChange_tmul, LinearMap.baseChangePairing_tmul_tmul]
      using congrArg (fun r ↦ a * b * algebraMap R S r) h
  root_weightMap := by
    ext i
    simp [f.root_weightMap_apply]
  coroot_coweightMap := by
    ext i
    simp [f.coroot_coweightMap_apply]

/-- The weight map of `f.baseChange S` is the base change of `f.weightMap`. -/
@[simp]
theorem baseChange_weightMap (f : P.Hom Q) :
    (f.baseChange S).weightMap = f.weightMap.baseChange S :=
  (rfl)

/-- The coweight map of `f.baseChange S` is the base change of `f.coweightMap`. -/
@[simp]
theorem baseChange_coweightMap (f : P.Hom Q) :
    (f.baseChange S).coweightMap = f.coweightMap.baseChange S :=
  (rfl)

/-- Scalar extension leaves the root-index bijection of a morphism unchanged. -/
@[simp]
theorem baseChange_indexEquiv (f : P.Hom Q) :
    (f.baseChange S).indexEquiv = f.indexEquiv :=
  (rfl)

omit [Free R N₂] [Module.Finite R N₂] in
variable (P) in
/-- Scalar extension preserves the identity morphism. -/
@[simp]
theorem baseChange_id :
    (Hom.id P).baseChange S = Hom.id (P.baseChange S) :=
  ext_weightMap LinearMap.baseChange_id

/-- Scalar extension preserves composition of morphisms of root pairings. -/
@[simp]
theorem baseChange_comp [Free R N₃] [Module.Finite R N₃] (g : Q.Hom T) (f : P.Hom Q) :
    (g.comp f).baseChange S = (g.baseChange S).comp (f.baseChange S) :=
  ext_weightMap (LinearMap.baseChange_comp f.weightMap g.weightMap)

/-- Extending scalars of morphisms along a faithful algebra is injective. -/
theorem baseChange_injective :
    Injective (fun f : P.Hom Q ↦ f.baseChange S) := by
  intro f g hfg
  refine ext_weightMap (LinearMap.ext fun m ↦ Q.tensorProduct_mk_injective S ?_)
  simpa using congr($(congrArg Hom.weightMap hfg) (1 ⊗ₜ[R] m))

end Hom

namespace Equiv

variable {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} {T : RootPairing ι₃ R M₃ N₃}
  [Free R N] [Module.Finite R N] [Free R N₂] [Module.Finite R N₂]

/-- **Extension of scalars of an equivalence of root pairings.** Both the weight and coweight
equivalences extend to `S`-linear equivalences on `S ⊗[R] -`. -/
noncomputable def baseChange (e : P.Equiv Q) : (P.baseChange S).Equiv (Q.baseChange S) where
  toHom := e.toHom.baseChange S
  bijective_weightMap := (e.weightEquiv.baseChange R S M M₂).bijective
  bijective_coweightMap := (e.coweightEquiv.baseChange R S N₂ N).bijective

/-- The morphism underlying `e.baseChange S` is the base change of `e.toHom`. -/
@[simp]
theorem baseChange_toHom (e : P.Equiv Q) :
    (e.baseChange S).toHom = e.toHom.baseChange S :=
  (rfl)

/-- The weight equivalence of `e.baseChange S` is the base change of `e.weightEquiv`. -/
@[simp]
theorem baseChange_weightEquiv (e : P.Equiv Q) :
    (e.baseChange S).weightEquiv = e.weightEquiv.baseChange R S M M₂ :=
  LinearEquiv.toLinearMap_injective rfl

/-- The coweight equivalence of `e.baseChange S` is the base change of `e.coweightEquiv`. -/
@[simp]
theorem baseChange_coweightEquiv (e : P.Equiv Q) :
    (e.baseChange S).coweightEquiv = e.coweightEquiv.baseChange R S N₂ N :=
  LinearEquiv.toLinearMap_injective rfl

/-- The forward coweight equivalence `(e.baseChange S).coweightEquiv.symm` is the base change of
`e.coweightEquiv.symm`. -/
theorem baseChange_coweightEquiv_symm (e : P.Equiv Q) :
    (e.baseChange S).coweightEquiv.symm = e.coweightEquiv.symm.baseChange R S N N₂ := by
  rw [baseChange_coweightEquiv, LinearEquiv.baseChange_symm]

/-- Scalar extension leaves the root-index bijection of an equivalence unchanged. -/
theorem baseChange_indexEquiv (e : P.Equiv Q) :
    (e.baseChange S).indexEquiv = e.indexEquiv :=
  (rfl)

omit [Free R N₂] [Module.Finite R N₂] in
variable (P) in
/-- Scalar extension preserves the identity equivalence. -/
@[simp]
theorem baseChange_id :
    (Equiv.id P).baseChange S = Equiv.id (P.baseChange S) := by
  have h := Hom.baseChange_id S P
  exact Equiv.ext (congrArg Hom.weightMap h) (congrArg Hom.coweightMap h) rfl

/-- Scalar extension preserves composition of equivalences of root pairings. -/
@[simp]
theorem baseChange_comp [Free R N₃] [Module.Finite R N₃] (g : Q.Equiv T) (f : P.Equiv Q) :
    (Equiv.comp g f).baseChange S = Equiv.comp (g.baseChange S) (f.baseChange S) := by
  have h := Hom.baseChange_comp S g.toHom f.toHom
  exact Equiv.ext (congrArg Hom.weightMap h) (congrArg Hom.coweightMap h) rfl

/-- Scalar extension commutes with inverting an equivalence of root pairings. -/
@[simp]
theorem baseChange_symm (e : P.Equiv Q) :
    (Equiv.symm P Q e).baseChange S =
      Equiv.symm (P.baseChange S) (Q.baseChange S) (e.baseChange S) := by
  refine Equiv.ext ?_ ?_ rfl
  · refine TensorProduct.AlgebraTensorModule.ext fun a m₂ ↦ ?_
    simp
  · refine TensorProduct.AlgebraTensorModule.ext fun a n ↦ ?_
    simp

omit [Free R N₂] [Module.Finite R N₂] in
/-- Scalar extension sends the reflection in `i` to the reflection of `P.baseChange S` in `i`. -/
@[simp]
theorem baseChange_reflection (i : ι) :
    (reflection P i).baseChange S = reflection (P.baseChange S) i := by
  apply weightHom_injective (P.baseChange S)
  refine LinearEquiv.toLinearMap_injective <| TensorProduct.AlgebraTensorModule.ext fun a m ↦ ?_
  simp

/-- Extending scalars of equivalences along a faithful algebra is injective. -/
theorem baseChange_injective :
    Injective (fun e : P.Equiv Q ↦ e.baseChange S) := fun _ _ h ↦ by
  have hhom := Hom.baseChange_injective S (congrArg Equiv.toHom h)
  exact Equiv.ext (congrArg Hom.weightMap hhom) (congrArg Hom.coweightMap hhom)
    (congrArg Hom.indexEquiv hhom)

end Equiv

end BaseChange

section AutBaseChange

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (S : Type*) [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [Free R N] [Module.Finite R N]

/-- **Extension of scalars of automorphisms**, as a group homomorphism
`P.Aut →* (P.baseChange S).Aut`. -/
noncomputable def autBaseChangeHom : P.Aut →* (P.baseChange S).Aut where
  toFun g := g.baseChange S
  map_one' := Equiv.baseChange_id S P
  map_mul' g h := Equiv.baseChange_comp S g h

/-- `RootPairing.autBaseChangeHom` acts by `RootPairing.Equiv.baseChange`. -/
theorem autBaseChangeHom_apply (g : P.Aut) :
    P.autBaseChangeHom S g = g.baseChange S :=
  (rfl)

/-- Scalar extension of automorphisms along a faithful algebra is injective. -/
theorem autBaseChangeHom_injective : Injective (P.autBaseChangeHom S) :=
  Equiv.baseChange_injective S

/-- The extended automorphism acts on pure weight tensors through the original weight action. -/
@[simp]
theorem autBaseChangeHom_smul_tmul (g : P.Aut) (a : S) (m : M) :
    P.autBaseChangeHom S g • (a ⊗ₜ[R] m) = a ⊗ₜ[R] (g • m) := by
  -- The `Aut` action on weights is defined as evaluation of `weightEquiv`.
  change (P.autBaseChangeHom S g).weightEquiv (a ⊗ₜ[R] m) = a ⊗ₜ[R] g.weightEquiv m
  rw [autBaseChangeHom_apply, Equiv.baseChange_weightEquiv, LinearEquiv.baseChange_tmul]

/-- The forward coweight action of the extended automorphism acts on pure tensors through the
forward coweight action of `g`. -/
@[simp]
theorem autBaseChangeHom_coweightEquiv_symm_tmul (g : P.Aut) (a : S) (n : N) :
    (P.autBaseChangeHom S g).coweightEquiv.symm (a ⊗ₜ[R] n) = a ⊗ₜ[R] g.coweightEquiv.symm n := by
  rw [autBaseChangeHom_apply, Equiv.baseChange_coweightEquiv_symm, LinearEquiv.baseChange_tmul]

/-- Scalar extension leaves the root-index permutation of an automorphism unchanged. -/
@[simp]
theorem autBaseChangeHom_indexEquiv (g : P.Aut) :
    (P.autBaseChangeHom S g).indexEquiv = g.indexEquiv :=
  (rfl)

/-- Scalar extension sends each root reflection to the reflection of `P.baseChange S` in the same
index. -/
@[simp]
theorem autBaseChangeHom_reflection (i : ι) :
    P.autBaseChangeHom S (Equiv.reflection P i) = Equiv.reflection (P.baseChange S) i :=
  Equiv.baseChange_reflection S i

/-- **Scalar extension carries `P.weylGroup` onto `(P.baseChange S).weylGroup`.** -/
theorem weylGroup_map_autBaseChangeHom :
    P.weylGroup.map (P.autBaseChangeHom S) = (P.baseChange S).weylGroup := by
  rw [weylGroup, weylGroup, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [mem_image, mem_range]
  exact ⟨by rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, (P.autBaseChangeHom_reflection S i).symm⟩,
    by rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, P.autBaseChangeHom_reflection S i⟩⟩

/-- An extended automorphism lies in the Weyl group of `P.baseChange S` if and only if the
original automorphism lies in `P.weylGroup`. -/
@[simp]
theorem autBaseChangeHom_mem_weylGroup_iff {g : P.Aut} :
    P.autBaseChangeHom S g ∈ (P.baseChange S).weylGroup ↔ g ∈ P.weylGroup := by
  rw [← P.weylGroup_map_autBaseChangeHom S]
  exact ⟨fun ⟨h, hh, heq⟩ ↦ P.autBaseChangeHom_injective S heq ▸ hh, fun hg ↦ ⟨g, hg, rfl⟩⟩

/-- **Scalar extension identifies the Weyl group of `P` with that of `P.baseChange S`.** -/
noncomputable def weylGroupBaseChangeMulEquiv :
    P.weylGroup ≃* (P.baseChange S).weylGroup :=
  (P.weylGroup.equivMapOfInjective (P.autBaseChangeHom S)
    (P.autBaseChangeHom_injective S)).trans
    (MulEquiv.subgroupCongr (P.weylGroup_map_autBaseChangeHom S))

/-- Coercing `weylGroupBaseChangeMulEquiv` to `(P.baseChange S).Aut` applies `autBaseChangeHom`. -/
@[simp]
theorem coe_weylGroupBaseChangeMulEquiv_apply (w : P.weylGroup) :
    (P.weylGroupBaseChangeMulEquiv S w : (P.baseChange S).Aut) = P.autBaseChangeHom S w :=
  (rfl)

/-- The Weyl-group isomorphism acts on pure tensors through the Weyl action of `P`. -/
@[simp]
theorem weylGroupBaseChangeMulEquiv_smul_tmul (w : P.weylGroup) (a : S) (m : M) :
    P.weylGroupBaseChangeMulEquiv S w • (a ⊗ₜ[R] m) = a ⊗ₜ[R] (w • m) :=
  P.autBaseChangeHom_smul_tmul S w a m

/-- Scalar extension sends the indexed reflection `ofIdx P i` to `ofIdx (P.baseChange S) i`. -/
@[simp]
theorem weylGroupBaseChangeMulEquiv_ofIdx (i : ι) :
    P.weylGroupBaseChangeMulEquiv S (weylGroup.ofIdx P i) =
      weylGroup.ofIdx (P.baseChange S) i :=
  Subtype.ext (P.autBaseChangeHom_reflection S i)

/-- The inverse Weyl-group isomorphism sends `ofIdx (P.baseChange S) i` to `ofIdx P i`. -/
@[simp]
theorem weylGroupBaseChangeMulEquiv_symm_ofIdx (i : ι) :
    (P.weylGroupBaseChangeMulEquiv S).symm (weylGroup.ofIdx (P.baseChange S) i) =
      weylGroup.ofIdx P i := by
  rw [← P.weylGroupBaseChangeMulEquiv_ofIdx S i, MulEquiv.symm_apply_apply]

/-- Scalar extension preserves the root-index permutation of every Weyl-group element.

Not a `simp` lemma: `RootPairing.weylGroupToPerm` simplifies to `indexEquiv` via
`weylGroupToPerm_apply`. -/
theorem weylGroupToPerm_weylGroupBaseChangeMulEquiv (w : P.weylGroup) :
    (P.baseChange S).weylGroupToPerm (P.weylGroupBaseChangeMulEquiv S w) =
      P.weylGroupToPerm w :=
  (rfl)

end AutBaseChange

end RootPairing
