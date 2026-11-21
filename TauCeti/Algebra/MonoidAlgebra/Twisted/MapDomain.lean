/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic

/-!
# Functoriality of twisted monoid algebras

A monoid homomorphism `f : G →* H` pulling a factor set `β` on `H` back to `α` on `G` induces a
`k`-algebra homomorphism `TauCeti.TwistedMonoidAlgebra.mapDomain` from `twistedMonoidAlgebra k G α`
to `twistedMonoidAlgebra k H β`. In `TwistedMonoidAlgebra.basis` coordinates, `mapDomain` acts by
`Finsupp.mapDomain f`, preserving injectivity and surjectivity and vanishing outside `Set.range f`.

## Main definitions

* `TauCeti.TwistedMonoidAlgebra.mapDomain`: functorial algebra homomorphism on twisted monoid
  algebras.

## Main results

* `TauCeti.TwistedMonoidAlgebra.mapDomain_of`, `mapDomain_id`, `mapDomain_comp`,
  `basis_repr_mapDomain`, `mapDomain_injective`, `mapDomain_surjective`.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

variable {k G H K : Type*} [CommSemiring k] [Monoid G] [Monoid H] [Monoid K]
  {α : G → G → kˣ} {β : H → H → kˣ} {γ : K → K → kˣ}
  [IsFactorSet α] [IsFactorSet β] [IsFactorSet γ]

/-- **Functoriality of the twisted monoid algebra.** A monoid homomorphism `f : G →* H` pulling the
factor set `β` back to `α` induces a `k`-algebra homomorphism `k_α[G] →ₐ[k] k_β[H]` sending
`of g` to `of (f g)`. -/
noncomputable def mapDomain (f : G →* H) (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂) :
    twistedMonoidAlgebra k G α →ₐ[k] twistedMonoidAlgebra k H β :=
  lift (fun g ↦ of (f g)) (by simp) (fun g₁ g₂ ↦ by simp [← map_mul, hf])

@[simp] theorem mapDomain_of (f : G →* H) (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂) (g : G) :
    mapDomain (k := k) f hf (of g) = of (f g) := lift_of ..

@[simp] theorem mapDomain_id :
    mapDomain (k := k) (α := α) (β := α) (MonoidHom.id G) (fun _ _ ↦ rfl) =
      AlgHom.id k (twistedMonoidAlgebra k G α) := by ext g; simp

@[simp] theorem mapDomain_comp (g : H →* K) (hg : ∀ h₁ h₂, γ (g h₁) (g h₂) = β h₁ h₂)
    (f : G →* H) (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂) :
    (mapDomain (k := k) g hg).comp (mapDomain f hf) =
      mapDomain (g.comp f) (fun g₁ g₂ ↦ (hg (f g₁) (f g₂)).trans (hf g₁ g₂)) := by ext x; simp

/-- Pointwise form of `mapDomain_comp`. -/
theorem mapDomain_mapDomain (g : H →* K) (hg : ∀ h₁ h₂, γ (g h₁) (g h₂) = β h₁ h₂)
    (f : G →* H) (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂)
    (x : twistedMonoidAlgebra k G α) :
    mapDomain g hg (mapDomain f hf x) =
      mapDomain (g.comp f) (fun g₁ g₂ ↦ (hg (f g₁) (f g₂)).trans (hf g₁ g₂)) x :=
  DFunLike.congr_fun (mapDomain_comp g hg f hf) x

/-- In `TwistedMonoidAlgebra.basis`, `mapDomain f` pushes coordinates by `Finsupp.mapDomain f`. -/
@[simp] theorem basis_repr_mapDomain (f : G →* H) (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂)
    (x : twistedMonoidAlgebra k G α) :
    (basis k H β).repr (mapDomain f hf x) = Finsupp.mapDomain f ((basis k G α).repr x) :=
  LinearMap.congr_fun ((basis k G α).ext
    (f₁ := (basis k H β).repr.toLinearMap ∘ₗ (mapDomain (k := k) f hf).toLinearMap)
    (f₂ := Finsupp.lmapDomain k k f ∘ₗ (basis k G α).repr.toLinearMap) fun g ↦ by simp) x

/-- Along an injective `f`, the `f g`-coordinate of `mapDomain f hf x` is the `g`-coordinate. -/
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
  rw [basis_repr_mapDomain]; exact Finsupp.mapDomain_of_notMem_range _ h hh

/-- An injective factor-set-preserving monoid homomorphism induces an injective `mapDomain`. -/
theorem mapDomain_injective {f : G →* H} (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂)
    (hfinj : Function.Injective f) :
    Function.Injective (mapDomain (k := k) f hf) := fun _ _ hxy ↦
  (basis k G α).repr.injective <| Finsupp.mapDomain_injective hfinj <| by
    simpa only [basis_repr_mapDomain] using congrArg (basis k H β).repr hxy

/-- A surjective factor-set-preserving monoid homomorphism induces a surjective `mapDomain`. -/
theorem mapDomain_surjective {f : G →* H} (hf : ∀ g₁ g₂, β (f g₁) (f g₂) = α g₁ g₂)
    (hfsurj : Function.Surjective f) :
    Function.Surjective (mapDomain (k := k) f hf) := fun y ↦ by
  obtain ⟨c, hc⟩ := Finsupp.mapDomain_surjective hfsurj ((basis k H β).repr y)
  exact ⟨(basis k G α).repr.symm c,
    (basis k H β).repr.injective (by rw [basis_repr_mapDomain, LinearEquiv.apply_symm_apply, hc])⟩

end TauCeti.TwistedMonoidAlgebra
