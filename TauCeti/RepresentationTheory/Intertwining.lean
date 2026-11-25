/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Stabilizer
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Intertwining maps: images, and the action of the monoid algebra

Mathlib records the image of an intertwining map as a subrepresentation
(`Representation.IntertwiningMap.range`) and turns a bijective intertwining map into an
equivalence (`Representation.IntertwiningMap.ofBijective`), but it does not connect the two: an
*injective* intertwining map is an isomorphism onto its image, and that is the usual way a
construction "`W` is the subrepresentation cut out by such and such an operator" is turned into an
identification of `W` with a representation built independently.

This file supplies the corestriction and that identification. The subrepresentation is taken as an
argument together with a proof that the image fills it, rather than being fixed to be
`IntertwiningMap.range f`: in practice the target subrepresentation is defined some other way -- as
the range of a different operator, say -- and matching the two ranges is a separate step that the
caller has already done.

The file also restricts intertwining maps and equivalences along a monoid homomorphism
`f : H →* G`, keeping the underlying linear map. This is the unbundled form of `Rep.resFunctor`,
and it is how an equivalence of representations of `G` is passed to a subgroup, for instance before
taking invariants under it.

## Main definitions

* `Representation.IntertwiningMap.codRestrict`: corestrict an intertwining map to a
  subrepresentation containing its image.
* `Representation.IntertwiningMap.equivOfRange`: an injective intertwining map is an equivalence
  onto a subrepresentation that its image fills.
* `Representation.IntertwiningMap.prodEquiv`: intertwining maps into a product are pairs of
  intertwining maps into the factors.
* `Representation.IntertwiningMap.lcomp`: precomposition with an intertwining map, as an
  intertwining map of the conjugation representations `Representation.linHom`.
* `Representation.IntertwiningMap.res` and `Representation.Equiv.res`: restriction of an
  intertwining map or an equivalence along a monoid homomorphism `H →* G`.
* `DistribMulActionHom.toIntertwiningMap`: an equivariant additive map of `G`-modules, as an
  intertwining map of the attached representations over `ℤ`.
* `Representation.Equiv.tprod`: the tensor product of two equivalences of representations.
* `Representation.Equiv.prodCongr`: the product of two equivalences of representations.
* `Representation.Equiv.dual`: the dual of an equivalence of representations.
* `Representation.IntertwiningMap.dualMap`: the transpose of an intertwining map, as an
  intertwining map of the dual representations, with its laws `IntertwiningMap.dualMap_id` and
  `IntertwiningMap.dualMap_comp`.
* `Representation.dualHomEquiv`: `Hom_G(V, W^*) ≃ Hom_G(W, V^*)` by swapping arguments.
* `Representation.Equiv.intertwiningMapCongr`: transport of intertwining maps along equivalences
  of the source and of the target.
* `Representation.Equiv.ofBasisAction`: build an equivalence from matching coordinate actions.
* `Representation.Equiv.ofClosureEqTop`: build an equivalence from equivariance on generators.

## Main results

* `Representation.IntertwiningMap.lcomp_comp_toLinearMap`: following an intertwining map into a
  conjugation representation by `lcomp u` is `compl₂` with `u` on the underlying bilinear maps.
* `Representation.IntertwiningMap.equivLinearMapAsModule_apply`: the attached module map acts
  by the original intertwining map on the underlying types.
* `Representation.IntertwiningMap.stabilizer_apply_eq_of_injective`: an injective intertwining
  map preserves stabilizers exactly, not only up to the inclusion `IntertwiningMap.stabilizer_le`.
* `Representation.IntertwiningMap.apply_asAlgebraHom`: an intertwining map commutes with the
  action of the monoid algebra, not only with that of the group elements.
* `Representation.IsIntertwiningMap.dualMap`: the transpose of an intertwining map intertwines
  the dual representations.
* `Representation.Equiv.ker_eq`: equivalent representations have the same kernel.
* `Representation.isIntertwiningMap_iff_of_closure_eq_top`: equivariance may be tested on a
  generating set of the group.
* `Representation.exists_unit_smul_of_intertwines`: if the equivariant endomorphisms of a
  nonzero representation are scalar, two invertible intertwiners out of it to the same target
  differ by a unit scalar.
* `AlgHom.isIntertwiningMap_toMonoidHom_comp_iff_of_span_eq_top`: equivariance under a monoid
  acting through a spanning image in an algebra is equivariance under the whole algebra.

-/

public section

namespace Representation.IntertwiningMap

/-- Two intertwining maps out of a product agree if they agree on both inclusions. -/
@[ext 1100]
theorem prod_ext {A G V W U : Type*} [Semiring A] [Monoid G]
    [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
    [AddCommMonoid U] [Module A U]
    {ρ : Representation A G V} {σ : Representation A G W} {τ : Representation A G U}
    {f g : IntertwiningMap (ρ.prod σ) τ}
    (hl : f.comp (inl A ρ σ) = g.comp (inl A ρ σ))
    (hr : f.comp (inr A ρ σ) = g.comp (inr A ρ σ)) : f = g := by
  apply ext
  apply LinearMap.prod_ext
  -- The underlying linear maps of the inclusions and compositions are definitionally
  -- `LinearMap.inl`, `LinearMap.inr`, and `LinearMap.comp`.
  · exact congrArg IntertwiningMap.toLinearMap hl
  · exact congrArg IntertwiningMap.toLinearMap hr

section prodEquiv

variable {A G V W U : Type*} [CommSemiring A] [Monoid G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W] [AddCommMonoid U] [Module A U]
  {ρ : Representation A G V} {σ : Representation A G W} {τ : Representation A G U}

/-- **Intertwining maps into a product are pairs of intertwining maps**: the representation
counterpart of `LinearMap.prodEquiv`, sending a pair `(f, g)` to `IntertwiningMap.prod f g`. -/
noncomputable def prodEquiv :
    (IntertwiningMap ρ σ × IntertwiningMap ρ τ) ≃ₗ[A] IntertwiningMap ρ (σ.prod τ) where
  toFun f := f.1.prod f.2
  invFun f := ((fst A σ τ).comp f, (snd A σ τ).comp f)
  left_inv f := by simp
  right_inv f := by ext <;> rfl
  map_add' f g := by ext <;> rfl
  map_smul' c f := by ext <;> rfl

@[simp]
theorem prodEquiv_apply (f : IntertwiningMap ρ σ × IntertwiningMap ρ τ) :
    prodEquiv f = f.1.prod f.2 :=
  (rfl)

@[simp]
theorem prodEquiv_symm_apply (f : IntertwiningMap ρ (σ.prod τ)) :
    prodEquiv.symm f = ((fst A σ τ).comp f, (snd A σ τ).comp f) :=
  (rfl)

end prodEquiv

/-- **Evaluation of the `k[G]`-linear map attached to an intertwining map.** The map
`Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f` is `f` itself on the underlying
types, so it too may be erased from an application. -/
@[simp]
theorem equivLinearMapAsModule_apply
    {k G V W : Type*} [CommSemiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (f : IntertwiningMap ρ σ) (x : ρ.asModule) :
    equivLinearMapAsModule ρ σ f x = (f (x : V) : W) :=
  (rfl)

section codRestrict

variable {A G V W : Type*} [Semiring A] [Monoid G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

/-- Corestrict an intertwining map to a subrepresentation of the target containing its image. -/
def codRestrict (f : IntertwiningMap ρ σ) (P : Subrepresentation σ)
    (hP : ∀ v, f v ∈ P.toSubmodule) : IntertwiningMap ρ P.toRepresentation where
  toLinearMap := LinearMap.codRestrict P.toSubmodule f.toLinearMap hP
  isIntertwining' g :=
    LinearMap.ext fun v =>
      Subtype.ext (congrArg (fun l : V →ₗ[A] W => l v) (f.isIntertwining' g))

@[simp]
theorem codRestrict_apply_coe (f : IntertwiningMap ρ σ) (P : Subrepresentation σ)
    (hP : ∀ v, f v ∈ P.toSubmodule) (v : V) :
    ((f.codRestrict P hP v : P.toSubmodule) : W) = f v := by
  rfl

/-- **An injective intertwining map is an isomorphism onto its image**, here onto any
subrepresentation `P` that the image fills. -/
noncomputable def equivOfRange (f : IntertwiningMap ρ σ) (hf : Function.Injective f)
    {P : Subrepresentation σ} (hP : LinearMap.range f.toLinearMap = P.toSubmodule) :
    ρ.Equiv P.toRepresentation :=
  let f' := f.codRestrict P fun v => hP.le (LinearMap.mem_range_self _ v)
  .mk (LinearEquiv.ofBijective f'.toLinearMap
    ⟨fun _ _ h => hf (by exact congrArg Subtype.val h), fun w => by
      obtain ⟨v, hv⟩ := hP.ge w.property
      exact ⟨v, Subtype.ext (by exact hv)⟩⟩) f'.isIntertwining'

@[simp]
theorem equivOfRange_apply_coe (f : IntertwiningMap ρ σ) (hf : Function.Injective f)
    {P : Subrepresentation σ} (hP : LinearMap.range f.toLinearMap = P.toSubmodule) (v : V) :
    ((f.equivOfRange hf hP v : P.toSubmodule) : W) = f v := by
  rfl

end codRestrict

variable {A G V W : Type*} [CommSemiring A] [Monoid G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

/-- **An intertwining map commutes with the action of the monoid algebra**, not only with that of
the group elements. -/
@[simp]
theorem apply_asAlgebraHom (f : IntertwiningMap ρ σ) (r : MonoidAlgebra A G) (v : V) :
    f (ρ.asAlgebraHom r v) = σ.asAlgebraHom r (f v) :=
  (equivLinearMapAsModule ρ σ f).map_smul r (ρ.asModuleEquiv.symm v)

section lcomp

variable {A G V V' W : Type*} [CommSemiring A] [Group G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid V'] [Module A V'] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {ρ' : Representation A G V'}

/-- **Precomposition with an intertwining map.** An intertwining map `u : ρ' → ρ` induces the
intertwining map `φ ↦ φ ∘ u` from the conjugation representation `linHom ρ σ` to
`linHom ρ' σ`. -/
def lcomp (u : IntertwiningMap ρ' ρ) (σ : Representation A G W) :
    IntertwiningMap (linHom ρ σ) (linHom ρ' σ) where
  toLinearMap := LinearMap.lcomp A W u.toLinearMap
  isIntertwining' g := by
    ext φ v
    simp [linHom_apply, IntertwiningMap.isIntertwining]

@[simp]
theorem lcomp_apply (u : IntertwiningMap ρ' ρ) (σ : Representation A G W) (φ : V →ₗ[A] W) :
    u.lcomp σ φ = φ ∘ₗ u.toLinearMap :=
  (rfl)

/-- Composing an intertwining map `q : ρ₀ → linHom ρ σ` into a conjugation representation with
precomposition by `u` is `q.compl₂ u` on the underlying bilinear maps. -/
theorem lcomp_comp_toLinearMap {V₀ : Type*} [AddCommMonoid V₀] [Module A V₀]
    {ρ₀ : Representation A G V₀} (u : IntertwiningMap ρ' ρ) (σ : Representation A G W)
    (q : IntertwiningMap ρ₀ (linHom ρ σ)) :
    ((u.lcomp σ).comp q).toLinearMap = q.toLinearMap.compl₂ u.toLinearMap :=
  (rfl)

end lcomp

section Restriction

variable {A G H V W U : Type*} [Semiring A] [Monoid G] [Monoid H]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W] [AddCommMonoid U] [Module A U]
  {ρ : Representation A G V} {σ : Representation A G W} {τ : Representation A G U}

/-- **Restriction of an intertwining map** along a monoid homomorphism `f : H →* G`: the same
linear map intertwines the restricted representations `ρ ∘ f` and `σ ∘ f` of `H`. This is the
unbundled counterpart of `Rep.resFunctor` on morphisms. -/
def res (φ : IntertwiningMap ρ σ) (f : H →* G) : IntertwiningMap (ρ.comp f) (σ.comp f) where
  toLinearMap := φ.toLinearMap
  isIntertwining' h := φ.isIntertwining' (f h)

@[simp]
theorem coe_res (φ : IntertwiningMap ρ σ) (f : H →* G) : ⇑(φ.res f) = φ :=
  (rfl)

@[simp]
theorem toLinearMap_res (φ : IntertwiningMap ρ σ) (f : H →* G) :
    (φ.res f).toLinearMap = φ.toLinearMap :=
  (rfl)

@[simp]
theorem res_id (f : H →* G) : (IntertwiningMap.id ρ).res f = .id (ρ.comp f) :=
  (rfl)

@[simp]
theorem res_comp (ψ : IntertwiningMap σ τ) (φ : IntertwiningMap ρ σ) (f : H →* G) :
    (ψ.comp φ).res f = (ψ.res f).comp (φ.res f) :=
  (rfl)

end Restriction

section Stabilizer

variable {A G V W : Type*} [Semiring A] [Group G] [AddCommMonoid V] [AddCommMonoid W]
  [Module A V] [Module A W] {ρ : Representation A G V} {σ : Representation A G W}

/-- **An injective intertwining map preserves stabilizers.** Mathlib's
`Representation.IntertwiningMap.stabilizer_le` gives one inclusion for any intertwining map;
injectivity gives the other, since `σ g (f v) = f v` reads `f (ρ g v) = f v`. -/
theorem stabilizer_apply_eq_of_injective (f : IntertwiningMap ρ σ) (hf : Function.Injective f)
    (v : V) : stabilizer σ (f v) = stabilizer ρ v := by
  ext g
  rw [mem_stabilizer, mem_stabilizer, ← isIntertwining _ _ f g v, hf.eq_iff]

end Stabilizer

end Representation.IntertwiningMap

namespace Representation.Equiv

section Product

variable {A G V V' W W' : Type*} [Semiring A] [Monoid G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid V'] [Module A V']
  [AddCommMonoid W] [Module A W] [AddCommMonoid W'] [Module A W']
  {ρ : Representation A G V} {ρ' : Representation A G V'}
  {σ : Representation A G W} {σ' : Representation A G W'}

/-- The product of two equivalences of representations, acting componentwise. -/
noncomputable def prodCongr (e : Equiv ρ ρ') (e' : Equiv σ σ') : Equiv (ρ.prod σ) (ρ'.prod σ') :=
  .mk (e.toLinearEquiv.prodCongr e'.toLinearEquiv) fun g ↦
    LinearMap.ext fun v ↦ Prod.ext
      (e.toIntertwiningMap.isIntertwining _ _ g v.1)
      (e'.toIntertwiningMap.isIntertwining _ _ g v.2)

/-- The linear equivalence underlying a product equivalence is the product of its factors. -/
@[simp]
theorem toLinearEquiv_prodCongr (e : Equiv ρ ρ') (e' : Equiv σ σ') :
    (e.prodCongr e').toLinearEquiv = e.toLinearEquiv.prodCongr e'.toLinearEquiv := (rfl)

/-- Forgetting equivariance of a product equivalence gives the product linear map. -/
@[simp]
theorem toLinearMap_prodCongr (e : Equiv ρ ρ') (e' : Equiv σ σ') :
    (e.prodCongr e').toLinearMap = e.toLinearMap.prodMap e'.toLinearMap := (rfl)

/-- A product equivalence acts on the two coordinates separately. -/
@[simp]
theorem prodCongr_apply (e : Equiv ρ ρ') (e' : Equiv σ σ') (v : V × W) :
    e.prodCongr e' v = (e v.1, e' v.2) := (rfl)

/-- Inverting a product equivalence inverts each factor. -/
@[simp]
theorem prodCongr_symm (e : Equiv ρ ρ') (e' : Equiv σ σ') :
    (e.prodCongr e').symm = e.symm.prodCongr e'.symm := by
  ext v <;> rfl

end Product

section Basis

variable {A G V W ι : Type*} [Semiring A] [Monoid G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W] [Finite ι]

/-- A linear identification with a based module is an equivalence of representations when the
two actions have the same coordinates in that basis. -/
noncomputable def ofBasisAction (ρ : Representation A G V)
    (σ : Representation A G (ι → A)) (e : V ≃ₗ[A] W) (b : Module.Basis ι A W)
    (a : G → W →ₗ[A] W) (haction : ∀ g v, e (ρ g v) = a g (e v))
    (hcoordinates : ∀ g w, σ g (b.repr w) = b.repr (a g w)) : ρ.Equiv σ := by
  refine .mk (e.trans b.equivFun) ?_
  intro g
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [haction]
  exact (hcoordinates g (e v)).symm

/-- The equivalence built by `ofBasisAction` sends a vector to its coordinates after applying the
given linear equivalence. -/
@[simp]
theorem ofBasisAction_apply (ρ : Representation A G V)
    (σ : Representation A G (ι → A)) (e : V ≃ₗ[A] W) (b : Module.Basis ι A W)
    (a : G → W →ₗ[A] W) (haction : ∀ g v, e (ρ g v) = a g (e v))
    (hcoordinates : ∀ g w, σ g (b.repr w) = b.repr (a g w)) (v : V) :
    ofBasisAction ρ σ e b a haction hcoordinates v = b.equivFun (e v) :=
  (rfl)

/-- The inverse of the equivalence built by `ofBasisAction` reconstructs a vector from its
coordinates and applies the inverse of the given linear equivalence. -/
@[simp]
theorem ofBasisAction_symm_apply (ρ : Representation A G V)
    (σ : Representation A G (ι → A)) (e : V ≃ₗ[A] W) (b : Module.Basis ι A W)
    (a : G → W →ₗ[A] W) (haction : ∀ g v, e (ρ g v) = a g (e v))
    (hcoordinates : ∀ g w, σ g (b.repr w) = b.repr (a g w)) (w : ι → A) :
    (ofBasisAction ρ σ e b a haction hcoordinates).symm w =
      e.symm (b.equivFun.symm w) :=
  (rfl)

end Basis

section Restriction

variable {A G H V W U : Type*} [Semiring A] [Monoid G] [Monoid H]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W] [AddCommMonoid U] [Module A U]
  {ρ : Representation A G V} {σ : Representation A G W} {τ : Representation A G U}

/-- **Restriction of an equivalence of representations** along a monoid homomorphism
`f : H →* G`: the same linear isomorphism is an equivalence between the restricted
representations `ρ ∘ f` and `σ ∘ f` of `H`. This is the unbundled counterpart of
`Rep.resFunctor` on isomorphisms. -/
def res (e : Equiv ρ σ) (f : H →* G) : Equiv (ρ.comp f) (σ.comp f) :=
  .mk e.toLinearEquiv (e.toIntertwiningMap.res f).isIntertwining'

@[simp]
theorem res_apply (e : Equiv ρ σ) (f : H →* G) (v : V) : e.res f v = e v :=
  (rfl)

@[simp]
theorem toIntertwiningMap_res (e : Equiv ρ σ) (f : H →* G) :
    (e.res f).toIntertwiningMap = e.toIntertwiningMap.res f :=
  (rfl)

@[simp]
theorem symm_res (e : Equiv ρ σ) (f : H →* G) : (e.res f).symm = e.symm.res f :=
  (rfl)

@[simp]
theorem res_refl (f : H →* G) : (refl ρ).res f = refl (ρ.comp f) :=
  (rfl)

@[simp]
theorem res_trans (e : Equiv ρ σ) (e' : Equiv σ τ) (f : H →* G) :
    (e.trans e').res f = (e.res f).trans (e'.res f) :=
  (rfl)

end Restriction

section Tensor

variable {A G V V' W W' : Type*} [CommSemiring A] [Monoid G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid V'] [Module A V']
  [AddCommMonoid W] [Module A W] [AddCommMonoid W'] [Module A W']
  {ρ : Representation A G V} {ρ' : Representation A G V'}
  {σ : Representation A G W} {σ' : Representation A G W'}

/-- **The tensor product of two equivalences of representations**, an equivalence
`ρ ⊗ σ ≃ ρ' ⊗ σ'` acting as `e₁ ⊗ e₂` on the underlying modules. -/
noncomputable def tprod (e₁ : Equiv ρ ρ') (e₂ : Equiv σ σ') :
    Equiv (ρ.tprod σ) (ρ'.tprod σ') :=
  .mk (TensorProduct.congr e₁.toLinearEquiv e₂.toLinearEquiv) fun g ↦
    TensorProduct.ext' fun v w ↦ by
      simp [IntertwiningMap.isIntertwining ρ ρ' e₁.toIntertwiningMap,
        IntertwiningMap.isIntertwining σ σ' e₂.toIntertwiningMap]

@[simp]
theorem tprod_tmul (e₁ : Equiv ρ ρ') (e₂ : Equiv σ σ') (v : V) (w : W) :
    e₁.tprod e₂ (v ⊗ₜ w) = e₁ v ⊗ₜ e₂ w :=
  (rfl)

end Tensor

section Dual

variable {A G V W : Type*} [CommSemiring A] [Group G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

/-- **The dual of an equivalence of representations**, an equivalence `ρ^∨ ≃ σ^∨` sending a
linear form `f` on `V` to `f ∘ e⁻¹`. -/
def dual (e : Equiv ρ σ) : Equiv ρ.dual σ.dual :=
  .mk e.toLinearEquiv.symm.dualMap fun g ↦ by
    ext f w
    simp only [dual_apply, Module.Dual.transpose_apply, LinearEquiv.coe_coe,
      LinearEquiv.dualMap_apply, LinearMap.comp_apply]
    exact congrArg f (IntertwiningMap.isIntertwining σ ρ e.symm.toIntertwiningMap g⁻¹ w).symm

@[simp]
theorem dual_apply_apply (e : Equiv ρ σ) (f : Module.Dual A V) (w : W) :
    e.dual f w = f (e.symm w) :=
  (rfl)

end Dual

section Kernel

variable {A G V W : Type*} [Semiring A] [Group G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

/-- Equivalent representations have the same kernel. -/
theorem ker_eq (e : Equiv ρ σ) : ρ.ker = σ.ker := by
  ext g
  have he := IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g
  simp only [coe_toIntertwiningMap] at he
  simp only [MonoidHom.mem_ker, LinearMap.ext_iff, one_apply_eq_self]
  refine ⟨fun h w ↦ ?_, fun h v ↦ EquivLike.injective e ?_⟩
  · obtain ⟨v, rfl⟩ := EquivLike.surjective e w
    rw [← he, h]
  · rw [he, h]

end Kernel

section Congr

variable {A G V V' W W' : Type*} [CommSemiring A] [Monoid G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid V'] [Module A V']
  [AddCommMonoid W] [Module A W] [AddCommMonoid W'] [Module A W']
  {ρ : Representation A G V} {ρ' : Representation A G V'}
  {σ : Representation A G W} {σ' : Representation A G W'}

/-- **Transport of intertwining maps along equivalences**: equivalences `e₁ : ρ ≃ ρ'` and
`e₂ : σ ≃ σ'` identify the intertwining maps `ρ → σ` with the intertwining maps `ρ' → σ'` by
`f ↦ e₂ ∘ f ∘ e₁⁻¹`. This is the unbundled form of `CategoryTheory.Iso.homCongr`, as a linear
equivalence. -/
def intertwiningMapCongr (e₁ : Equiv ρ ρ') (e₂ : Equiv σ σ') :
    IntertwiningMap ρ σ ≃ₗ[A] IntertwiningMap ρ' σ' where
  toFun f := e₂.toIntertwiningMap.comp (f.comp e₁.symm.toIntertwiningMap)
  invFun f := e₂.symm.toIntertwiningMap.comp (f.comp e₁.toIntertwiningMap)
  map_add' f g := IntertwiningMap.ext <| LinearMap.ext fun v => by simp
  map_smul' c f := IntertwiningMap.ext <| LinearMap.ext fun v => by simp
  left_inv f := IntertwiningMap.ext <| LinearMap.ext fun v => by simp
  right_inv f := IntertwiningMap.ext <| LinearMap.ext fun v => by simp

@[simp]
theorem intertwiningMapCongr_apply (e₁ : Equiv ρ ρ') (e₂ : Equiv σ σ') (f : IntertwiningMap ρ σ)
    (v : V') : intertwiningMapCongr e₁ e₂ f v = e₂ (f (e₁.symm v)) :=
  (rfl)

@[simp]
theorem intertwiningMapCongr_symm_apply (e₁ : Equiv ρ ρ') (e₂ : Equiv σ σ')
    (f : IntertwiningMap ρ' σ') (v : V) :
    (intertwiningMapCongr e₁ e₂).symm f v = e₂.symm (f (e₁ v)) :=
  (rfl)

end Congr

end Representation.Equiv

namespace Representation

/-- The transpose of an intertwining map intertwines the dual representations, in the reverse
direction. This is the unbundled counterpart of `Representation.Equiv.dual`, for maps that need
not be bijective. -/
theorem IsIntertwiningMap.dualMap {A G V W : Type*} [CommSemiring A] [Group G]
    [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W] {ρ : Representation A G V}
    {σ : Representation A G W} {f : V →ₗ[A] W} (hf : IsIntertwiningMap ρ σ f) :
    IsIntertwiningMap σ.dual ρ.dual f.dualMap :=
  ⟨fun g φ ↦ LinearMap.ext fun v ↦ congrArg φ (hf.isIntertwining g⁻¹ v).symm⟩

section DualMap

variable {A G V W : Type*} [CommSemiring A] [Group G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

/-- The transpose `σ^* → ρ^*`, `φ ↦ φ ∘ f`, of an intertwining map `f : ρ → σ`, bundled as an
intertwining map of the dual representations. -/
def IntertwiningMap.dualMap (f : IntertwiningMap ρ σ) : IntertwiningMap σ.dual ρ.dual :=
  f.toLinearMap.dualMap.intertwiningMap_of_isIntertwiningMap σ.dual ρ.dual
    (IsIntertwiningMap.dualMap ⟨f.isIntertwining⟩).isIntertwining

@[simp]
theorem IntertwiningMap.dualMap_apply_apply (f : IntertwiningMap ρ σ) (φ : Module.Dual A W)
    (v : V) : f.dualMap φ v = φ (f v) :=
  (rfl)

/-- Transposing the identity intertwining map gives the identity. -/
@[simp]
theorem IntertwiningMap.dualMap_id : (IntertwiningMap.id ρ).dualMap = IntertwiningMap.id ρ.dual :=
  (rfl)

/-- Transposing a composite reverses the order of its factors. -/
@[simp]
theorem IntertwiningMap.dualMap_comp {U : Type*} [AddCommMonoid U] [Module A U]
    {τ : Representation A G U} (f : IntertwiningMap ρ σ) (f' : IntertwiningMap σ τ) :
    (f'.comp f).dualMap = f.dualMap.comp f'.dualMap :=
  (rfl)

/-- Swapping the arguments of an intertwining map `V → W^*` gives an intertwining map `W → V^*`:
`f (ρ g⁻¹ v) w = f v (σ g w)`. -/
private theorem flip_intertwining (f : IntertwiningMap ρ σ.dual) (g : G) (w : W) :
    f.toLinearMap.flip (σ g w) = ρ.dual g (f.toLinearMap.flip w) :=
  LinearMap.ext fun v ↦ by simp [Module.Dual.transpose_apply, f.isIntertwining]

variable (ρ σ) in
/-- **Intertwining maps into a dual.** `Hom_G(V, W^*) ≃ Hom_G(W, V^*)` by swapping arguments,
`f ↦ (w ↦ (v ↦ f v w))`: both sides are the `G`-invariant bilinear pairings `V × W → A`. -/
def dualHomEquiv : IntertwiningMap ρ σ.dual ≃ₗ[A] IntertwiningMap σ ρ.dual where
  toFun f := f.toLinearMap.flip.intertwiningMap_of_isIntertwiningMap σ ρ.dual
    (flip_intertwining f)
  invFun f := f.toLinearMap.flip.intertwiningMap_of_isIntertwiningMap ρ σ.dual
    (flip_intertwining f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem dualHomEquiv_apply_apply (f : IntertwiningMap ρ σ.dual) (w : W) (v : V) :
    dualHomEquiv ρ σ f w v = f v w :=
  (rfl)

@[simp]
theorem dualHomEquiv_symm : (dualHomEquiv ρ σ).symm = dualHomEquiv σ ρ :=
  (rfl)

end DualMap

/-- **Equivariance may be tested on a generating set**: if `s` generates the group `G`, a linear
map intertwines `ρ` and `σ` exactly when it commutes with the action of every element of `s`. -/
theorem isIntertwiningMap_iff_of_closure_eq_top {A G V W : Type*} [Semiring A] [Group G]
    [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W] (ρ : Representation A G V)
    (σ : Representation A G W) {s : Set G} (hs : Subgroup.closure s = ⊤) (f : V →ₗ[A] W) :
    IsIntertwiningMap ρ σ f ↔ ∀ g ∈ s, ∀ v, f (ρ g v) = σ g (f v) := by
  refine ⟨fun hf g _ v ↦ hf.isIntertwining g v, fun h ↦ ⟨fun g ↦ ?_⟩⟩
  induction hs.ge (Subgroup.mem_top g) using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => simp
  | mul g g' _ _ hg hg' =>
    intro v
    rw [map_mul, mul_apply_eq_comp, hg, hg', map_mul, mul_apply_eq_comp]
  | inv g _ hg =>
    intro v
    calc f (ρ g⁻¹ v) = σ g⁻¹ (σ g (f (ρ g⁻¹ v))) := (σ.inv_self_apply g _).symm
      _ = σ g⁻¹ (f v) := by rw [← hg, ρ.self_inv_apply]

/-- If the equivariant endomorphisms of a nonzero representation `ρ` are scalar, two invertible
intertwiners from `ρ` to the same target `σ` differ by a unit scalar. Neither an algebraic closure
nor finite dimensionality is needed. -/
theorem exists_unit_smul_of_intertwines {k G V W : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [Nontrivial V]
    {ρ : Representation k G V} {σ : Representation k G W}
    (hscalar : ∀ f : Module.End k V, (∀ g, Commute f (ρ g)) →
      ∃ c : k, f = algebraMap k (Module.End k V) c)
    (a b : V ≃ₗ[k] W) (ha : ∀ g x, a (ρ g x) = σ g (a x))
    (hb : ∀ g x, b (ρ g x) = σ g (b x)) :
    ∃ c : kˣ, ∀ x, a x = (c : k) • b x := by
  obtain ⟨c, hc⟩ := hscalar ((b.symm : W →ₗ[k] V) ∘ₗ (a : V →ₗ[k] W)) fun g ↦ by
    refine (commute_iff_eq _ _).2 (LinearMap.ext fun x ↦ ?_)
    simp only [mul_apply_eq_comp, LinearMap.comp_apply, LinearEquiv.coe_coe, ha]
    rw [LinearEquiv.symm_apply_eq, hb, LinearEquiv.apply_symm_apply]
  have hx (x : V) : a x = c • b x := by
    have := LinearMap.congr_fun hc x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.algebraMap_end_apply] at this
    rw [← map_smul, ← this, LinearEquiv.apply_symm_apply]
  have hc₀ : c ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx₀⟩ := exists_ne (0 : V)
    exact hx₀ (a.injective (by simp [hx]))
  exact ⟨Units.mk0 c hc₀, hx⟩

/-- **Equivariance under a spanning monoid is equivariance under the whole algebra.** If the image
of `φ : H →* B` spans the `A`-algebra `B`, a linear map intertwines the restrictions along `φ` of
two algebra actions `F` and `G` exactly when it intertwines `F b` and `G b` for every `b : B`. -/
theorem _root_.AlgHom.isIntertwiningMap_toMonoidHom_comp_iff_of_span_eq_top {A B H V W : Type*}
    [CommSemiring A] [Semiring B] [Algebra A B] [Monoid H]
    [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
    (F : B →ₐ[A] Module.End A V) (G : B →ₐ[A] Module.End A W) (φ : H →* B)
    (hφ : Submodule.span A (Set.range φ) = ⊤) (f : V →ₗ[A] W) :
    IsIntertwiningMap ((F : B →* Module.End A V).comp φ) ((G : B →* Module.End A W).comp φ) f ↔
      ∀ b v, f (F b v) = G b (f v) := by
  -- The restricted actions act by `F (φ g)` and `G (φ g)`.
  simp only [isIntertwiningMap_iff, MonoidHom.comp_apply, AlgHom.coe_toMonoidHom]
  refine ⟨fun hf b v ↦ ?_, fun h g v ↦ h (φ g) v⟩
  -- Both sides are linear in `b`: `F b` postcomposed with `f`, and `G b` precomposed with `f`.
  have hext : LinearMap.llcomp A V V W f ∘ₗ F.toLinearMap =
      LinearMap.lcomp A W f ∘ₗ G.toLinearMap :=
    LinearMap.ext_on_range hφ fun g ↦ LinearMap.ext fun v ↦ by
      simpa only [LinearMap.coe_comp, AlgHom.coe_toLinearMap, Function.comp_apply,
        LinearMap.llcomp_apply, LinearMap.lcomp_apply] using hf g v
  exact LinearMap.congr_fun (LinearMap.congr_fun hext b) v

namespace Equiv

variable {A G V W : Type*} [Semiring A] [Group G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

/-- A linear equivalence commuting with the action of a generating set is an equivalence of
representations. -/
def ofClosureEqTop (f : V ≃ₗ[A] W) {s : Set G} (hs : Subgroup.closure s = ⊤)
    (h : ∀ g ∈ s, ∀ v, f (ρ g v) = σ g (f v)) : ρ.Equiv σ :=
  .mk f fun g => LinearMap.ext
    (((isIntertwiningMap_iff_of_closure_eq_top ρ σ hs f.toLinearMap).2 h).isIntertwining g)

/-- The equivalence constructed from equivariance on generators acts by the given linear
equivalence. -/
@[simp]
theorem ofClosureEqTop_apply (f : V ≃ₗ[A] W) {s : Set G} (hs : Subgroup.closure s = ⊤)
    (h : ∀ g ∈ s, ∀ v, f (ρ g v) = σ g (f v)) (v : V) :
    ofClosureEqTop f hs h v = f v :=
  (rfl)

/-- The inverse of the equivalence constructed from equivariance on generators acts by the inverse
of the given linear equivalence. -/
@[simp]
theorem ofClosureEqTop_symm_apply (f : V ≃ₗ[A] W) {s : Set G} (hs : Subgroup.closure s = ⊤)
    (h : ∀ g ∈ s, ∀ v, f (ρ g v) = σ g (f v)) (w : W) :
    (ofClosureEqTop f hs h).symm w = f.symm w :=
  (rfl)

end Equiv

end Representation

namespace DistribMulActionHom

open Representation

variable {G V W : Type*} [Monoid G] [AddCommGroup V] [DistribMulAction G V] [AddCommGroup W]
  [DistribMulAction G W]

/-- An equivariant additive map `f : V →+[G] W` of `G`-modules, as an intertwining map between the
representations `Representation.ofDistribMulAction ℤ G` on `V` and on `W`. -/
def toIntertwiningMap (f : V →+[G] W) :
    IntertwiningMap (ofDistribMulAction ℤ G V) (ofDistribMulAction ℤ G W) :=
  f.toAddMonoidHom.toIntLinearMap.intertwiningMap_of_isIntertwiningMap _ _ fun g v =>
    map_smul f g v

/-- The linear map underlying `f.toIntertwiningMap` is `f`, as a `ℤ`-linear map. -/
@[simp]
theorem toLinearMap_toIntertwiningMap (f : V →+[G] W) :
    f.toIntertwiningMap.toLinearMap = f.toAddMonoidHom.toIntLinearMap :=
  (rfl)

/-- `f.toIntertwiningMap` acts as `f`. -/
@[simp]
theorem coe_toIntertwiningMap (f : V →+[G] W) : ⇑f.toIntertwiningMap = ⇑f :=
  (rfl)

end DistribMulActionHom
