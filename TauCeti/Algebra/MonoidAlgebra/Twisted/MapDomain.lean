/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic

/-!
# Functoriality of twisted monoid algebras

A monoid homomorphism `f : G →* H` that pulls a factor set `β` on `H` back to `α` on `G`
(`∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂`) sends the basis elements of `twistedMonoidAlgebra k G α` to
those of `twistedMonoidAlgebra k H β` with matching multiplication table, so by
`TauCeti.TwistedMonoidAlgebra.lift` it induces an algebra homomorphism
`TauCeti.TwistedMonoidAlgebra.mapDomain`.

In coordinates with respect to `TauCeti.TwistedMonoidAlgebra.basis`, `mapDomain` acts by
`Finsupp.mapDomain f`. Consequently an injective monoid homomorphism induces an injective algebra
homomorphism whose image has coordinates supported on `Set.range f`, and a surjective monoid
homomorphism induces a surjective algebra homomorphism.

## Main definitions

* `TauCeti.TwistedMonoidAlgebra.mapDomain`: the `k`-algebra map
  `twistedMonoidAlgebra k G α →ₐ[k] twistedMonoidAlgebra k H β` induced by `f : G →* H`
  satisfying `∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂`.

## Main results

* `TauCeti.TwistedMonoidAlgebra.mapDomain_of`, `TauCeti.TwistedMonoidAlgebra.mapDomain_id`, and
  `TauCeti.TwistedMonoidAlgebra.mapDomain_comp`: generator rule and functor laws.
* `TauCeti.TwistedMonoidAlgebra.basis_repr_mapDomain`: coordinate representation via
  `Finsupp.mapDomain`.
* `TauCeti.TwistedMonoidAlgebra.mapDomain_injective` and
  `TauCeti.TwistedMonoidAlgebra.mapDomain_surjective`: preservation of injectivity and
  surjectivity.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

variable {k G H K : Type*} [CommSemiring k] [Monoid G] [Monoid H] [Monoid K]
  {α : G → G → kˣ} {β : H → H → kˣ} {γ : K → K → kˣ}
  [IsFactorSet α] [IsFactorSet β] [IsFactorSet γ]

/-- The basis representation of the basis element `of g` is `Finsupp.single g 1`. -/
@[simp]
theorem basis_repr_of (g : G) :
    (basis k G α).repr (of g) = Finsupp.single g 1 := by
  rw [← basis_apply, Module.Basis.repr_self]

/-- **Functoriality of the twisted monoid algebra.** A monoid homomorphism `f : G →* H` pulling the
factor set `β` back to `α` induces a `k`-algebra homomorphism `k_α[G] →ₐ[k] k_β[H]` sending
`of g` to `of (f g)`. -/
noncomputable def mapDomain (f : G →* H) (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂) :
    twistedMonoidAlgebra k G α →ₐ[k] twistedMonoidAlgebra k H β :=
  lift (fun g ↦ of (f g)) (by simp) (fun g₁ g₂ ↦ by simp [← map_mul, hf])

/-- `mapDomain` sends the basis element at `g` to the basis element at `f g`. -/
@[simp]
theorem mapDomain_of (f : G →* H) (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂) (g : G) :
    mapDomain (k := k) f hf (of g) = of (f g) :=
  lift_of ..

/-- `mapDomain` along the identity monoid homomorphism is the identity algebra homomorphism. -/
@[simp]
theorem mapDomain_id :
    mapDomain (k := k) (α := α) (β := α) (MonoidHom.id G) (fun _ _ ↦ rfl) =
      AlgHom.id k (twistedMonoidAlgebra k G α) := by
  ext g
  simp

/-- `mapDomain` preserves composition of factor-set-preserving monoid homomorphisms. -/
@[simp]
theorem mapDomain_comp (g : H →* K) (hg : ∀ h₁ h₂, γ (g h₁) (g h₂) = β h₁ h₂)
    (f : G →* H) (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂) :
    (mapDomain (k := k) g hg).comp (mapDomain f hf) =
      mapDomain (g.comp f) (fun g₁ g₂ ↦ (hg (f g₁) (f g₂)).trans (hf g₁ g₂)) := by
  ext x
  simp

/-- Pointwise form of `mapDomain_comp`. -/
theorem mapDomain_mapDomain (g : H →* K) (hg : ∀ h₁ h₂, γ (g h₁) (g h₂) = β h₁ h₂)
    (f : G →* H) (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂)
    (x : twistedMonoidAlgebra k G α) :
    mapDomain g hg (mapDomain f hf x) =
      mapDomain (g.comp f) (fun g₁ g₂ ↦ (hg (f g₁) (f g₂)).trans (hf g₁ g₂)) x :=
  DFunLike.congr_fun (mapDomain_comp g hg f hf) x

/-- In the basis `TwistedMonoidAlgebra.basis`, `mapDomain f` pushes coordinates forward by
`Finsupp.mapDomain f`. -/
@[simp]
theorem basis_repr_mapDomain (f : G →* H) (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂)
    (x : twistedMonoidAlgebra k G α) :
    (basis k H β).repr (mapDomain f hf x) = Finsupp.mapDomain f ((basis k G α).repr x) := by
  have hlin :
      (basis k H β).repr.toLinearMap ∘ₗ (mapDomain (k := k) f hf).toLinearMap =
        Finsupp.lmapDomain k k f ∘ₗ (basis k G α).repr.toLinearMap :=
    (basis k G α).ext fun g ↦ by simp
  exact LinearMap.congr_fun hlin x

/-- Along an injective monoid homomorphism `f`, the `f g`-coordinate of `mapDomain f hf x` is the
`g`-coordinate of `x`. -/
theorem basis_repr_mapDomain_apply_of_injective {f : G →* H}
    (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂) (hfinj : Function.Injective f)
    (x : twistedMonoidAlgebra k G α) (g : G) :
    (basis k H β).repr (mapDomain f hf x) (f g) = (basis k G α).repr x g := by
  rw [basis_repr_mapDomain, Finsupp.mapDomain_apply_of_injective hfinj]

/-- Coordinates of `mapDomain f hf x` vanish outside `Set.range f`. -/
theorem basis_repr_mapDomain_of_notMem_range (f : G →* H)
    (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂) (x : twistedMonoidAlgebra k G α) {h : H}
    (hh : h ∉ Set.range f) :
    (basis k H β).repr (mapDomain f hf x) h = 0 := by
  rw [basis_repr_mapDomain]
  exact Finsupp.mapDomain_of_notMem_range _ h hh

/-- An injective factor-set-preserving monoid homomorphism induces an injective algebra
homomorphism on twisted monoid algebras. -/
theorem mapDomain_injective {f : G →* H} (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂)
    (hfinj : Function.Injective f) :
    Function.Injective (mapDomain (k := k) f hf) := by
  intro x y hxy
  apply (basis k G α).repr.injective
  apply Finsupp.mapDomain_injective hfinj
  simpa only [basis_repr_mapDomain] using congrArg (basis k H β).repr hxy

/-- A surjective factor-set-preserving monoid homomorphism induces a surjective algebra
homomorphism on twisted monoid algebras. -/
theorem mapDomain_surjective {f : G →* H} (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂)
    (hfsurj : Function.Surjective f) :
    Function.Surjective (mapDomain (k := k) f hf) := by
  intro y
  obtain ⟨c, hc⟩ := Finsupp.mapDomain_surjective hfsurj ((basis k H β).repr y)
  refine ⟨(basis k G α).repr.symm c, (basis k H β).repr.injective ?_⟩
  rw [basis_repr_mapDomain, LinearEquiv.apply_symm_apply, hc]

end TauCeti.TwistedMonoidAlgebra
