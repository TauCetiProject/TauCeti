/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle

/-!
# One-cocycles on free groups and presented groups

Let `ρ` be a representation of a group `G` on a `k`-module `V`, and write `Z¹(G, V)` for Mathlib's
one-cocycles `groupCohomology.cocycles₁ (Rep.of ρ)`, the functions `f : G → V` with
`f (g * h) = ρ g (f h) + f g`. A one-cocycle is determined by its values on a generating set
(`groupCohomology.cocycles₁_ext_of_closure_eq_top`).

On a free group `F(X)` the values on the generators are arbitrary: evaluation at the generators
is a linear equivalence `Z¹(F(X), V) ≃ (X → V)` (`Representation.freeCocycleEquiv`). The cocycle
with prescribed values `v` is the translation part of the homomorphism from `F(X)` to the affine
automorphisms of `V` sending the generator `x` to `y ↦ ρ x y + v x`.

For a word `r` of `F(X)`, the **Fox map** of `r` is the linear map `(X → V) → V` sending `v` to
the value at `r` of the free cocycle with values `v` on the generators
(`Representation.foxMap`). In Fox's free differential calculus it is `v ↦ ∑ₓ ρ(∂r/∂x) (v x)`.
The Fox maps satisfy the product rule `∂(r s) = ∂r + r ∂s` (`Representation.foxMap_mul`), and
the Fox map of a product of commutators lands in the coinvariant kernel
`Representation.Coinvariants.ker ρ` (`Representation.range_foxMap_le_coinvariantsKer`).

For a presented group `G = ⟨X | R⟩` and a representation `ρ` of `G`, the Fox map of a word for
the representation pulled back to `F(X)` evaluates a one-cocycle of `G` at the image of the word
(`Representation.foxMap_cocyclesEvalOf`), and evaluation at the generators identifies `Z¹(G, V)`
with the common kernel of the Fox maps of the relators (`Representation.presentedCocyclesEquiv`):
a tuple `v` satisfying these relator conditions defines, through `PresentedGroup.toGroup`, a
homomorphism from `G` to the affine automorphisms of `V`, whose translation part is the cocycle.
This is the standard computation of `Z¹` from a presentation, used for surface groups in
`TauCeti.RepresentationTheory.Homological.GroupCohomology.SurfaceGroup`. In particular `Z¹(G, V)`
is a finite module when there are finitely many generators and `V` is finite over a Noetherian
ring.

## References

* R. H. Fox, *Free differential calculus. I. Derivation in the free group ring*, Annals of
  Mathematics 57 (1953), 547–560.
* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer, 1982,
  Chapter IV, §2 (derivations and cocycles).
-/

public section

open CategoryTheory groupCohomology

universe u w

namespace Representation

variable {k : Type u} [CommRing k] {X : Type u} {V : Type w} [AddCommGroup V] [Module k V]

section Free

variable (ρ : Representation k (FreeGroup X) V)

/-- The homomorphism from the free group to the affine automorphisms of `V` sending the
generator `x` to `y ↦ ρ x y + v x`. -/
private noncomputable def freeAffineHom (v : X → V) : FreeGroup X →* (V ≃ᵃ[k] V) :=
  FreeGroup.lift fun x ↦
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k V
      (ρ.asGroupHom (FreeGroup.of x))).toAffineEquiv.trans (AffineEquiv.constVAdd k V (v x))

private theorem linear_freeAffineHom (v : X → V) (w : FreeGroup X) (y : V) :
    (freeAffineHom ρ v w).linear y = ρ w y := by
  have : AffineEquiv.linearHom.comp (freeAffineHom ρ v) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom.comp ρ.asGroupHom :=
    FreeGroup.ext_hom _ _ fun x ↦ LinearEquiv.ext fun y ↦ by
      simp only [freeAffineHom, MonoidHom.coe_comp, Function.comp_apply, FreeGroup.lift_apply_of,
        AffineEquiv.linearHom_apply, MulEquiv.coe_toMonoidHom]
      -- Mathlib has no lemmas for the linear parts of `AffineEquiv.trans`,
      -- `AffineEquiv.constVAdd` and `LinearEquiv.toAffineEquiv`; by definition they are the
      -- composite, the identity and the linear equivalence itself, so the linear part of the
      -- generator's image is the unit `generalLinearEquiv k V (ρ.asGroupHom (of x))`.
      rfl
  simpa [asGroupHom_apply] using congrArg (fun φ ↦ (φ w : V ≃ₗ[k] V) y) this

/-- **The free cocycle with prescribed values on the generators.** On the free group `F(X)`, the
unique one-cocycle `c` for `ρ` with `c (of x) = v x` (`Representation.freeCocycle_of`). -/
noncomputable def freeCocycle (v : X → V) (w : FreeGroup X) : V :=
  freeAffineHom ρ v w 0

private theorem freeAffineHom_apply (v : X → V) (w : FreeGroup X) (y : V) :
    freeAffineHom ρ v w y = ρ w y + freeCocycle ρ v w := by
  have := (freeAffineHom ρ v w).map_vadd 0 y
  rw [vadd_eq_add, add_zero, linear_freeAffineHom, vadd_eq_add] at this
  rw [this, freeCocycle]

/-- The free cocycle satisfies the cocycle identity. -/
theorem freeCocycle_mul (v : X → V) (w w' : FreeGroup X) :
    freeCocycle ρ v (w * w') = ρ w (freeCocycle ρ v w') + freeCocycle ρ v w := by
  rw [freeCocycle, map_mul, AffineEquiv.coe_mul, Function.comp_apply, freeAffineHom_apply,
    ← freeCocycle]

/-- The free cocycle takes the prescribed values on the generators. -/
@[simp]
theorem freeCocycle_of (v : X → V) (x : X) : freeCocycle ρ v (FreeGroup.of x) = v x := by
  simp [freeCocycle, freeAffineHom]

/-- The free cocycle is a one-cocycle. -/
theorem freeCocycle_mem_cocycles₁ (v : X → V) : freeCocycle ρ v ∈ cocycles₁ (Rep.of ρ) :=
  (mem_cocycles₁_iff _).2 fun w w' ↦ freeCocycle_mul ρ v w w'

/-- **One-cocycles on a free group are free.** Evaluation at the generators is a linear
equivalence between the one-cocycles of `F(X)` and `X → V`; its inverse sends `v` to the free
cocycle `Representation.freeCocycle ρ v`. -/
noncomputable def freeCocycleEquiv : cocycles₁ (Rep.of ρ) ≃ₗ[k] (X → V) where
  toFun f x := f (FreeGroup.of x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨freeCocycle ρ v, freeCocycle_mem_cocycles₁ ρ v⟩
  left_inv f := cocycles₁_ext_of_closure_eq_top (FreeGroup.closure_range_of X) <| by
    rintro _ ⟨x, rfl⟩
    exact freeCocycle_of ρ _ x
  right_inv v := funext <| freeCocycle_of ρ v

@[simp]
theorem freeCocycleEquiv_apply (f : cocycles₁ (Rep.of ρ)) (x : X) :
    freeCocycleEquiv ρ f x = f (FreeGroup.of x) := (rfl)

@[simp]
theorem coe_freeCocycleEquiv_symm_apply (v : X → V) :
    ((freeCocycleEquiv ρ).symm v : FreeGroup X → V) = freeCocycle ρ v := (rfl)

/-- A one-cocycle on a free group is the free cocycle of its values on the generators. -/
theorem freeCocycle_comp_of (f : cocycles₁ (Rep.of ρ)) : freeCocycle ρ (f ∘ FreeGroup.of) = f :=
  congrArg (fun f : cocycles₁ (Rep.of ρ) ↦ (f : FreeGroup X → V))
    ((freeCocycleEquiv ρ).symm_apply_apply f)

/-- **The Fox map of a word `r`**: the value at `r` of the free cocycle, as a linear function of
its values on the generators. In Fox's free differential calculus it is `v ↦ ∑ₓ ρ(∂r/∂x) (v x)`. -/
noncomputable def foxMap (r : FreeGroup X) : (X → V) →ₗ[k] V :=
  (LinearMap.proj r ∘ₗ (cocycles₁ (Rep.of ρ)).subtype) ∘ₗ (freeCocycleEquiv ρ).symm.toLinearMap

theorem foxMap_apply (r : FreeGroup X) (v : X → V) : foxMap ρ r v = freeCocycle ρ v r := (rfl)

/-- The Fox map of a generator is evaluation at that generator. -/
@[simp]
theorem foxMap_of (x : X) (v : X → V) : foxMap ρ (FreeGroup.of x) v = v x :=
  freeCocycle_of ρ v x

/-- **The product rule for Fox maps**, `∂(r s) = ∂r + r ∂s`. -/
theorem foxMap_mul (r s : FreeGroup X) (v : X → V) :
    foxMap ρ (r * s) v = ρ r (foxMap ρ s v) + foxMap ρ r v :=
  freeCocycle_mul ρ v r s

/-- **The Fox map of a product of commutators lands in the coinvariant kernel.** If the word `r`
lies in the commutator subgroup of the free group, every value of its Fox map lies in the span of
the `ρ g y - y`. -/
theorem range_foxMap_le_coinvariantsKer {r : FreeGroup X} (hr : r ∈ commutator (FreeGroup X)) :
    LinearMap.range (foxMap ρ r) ≤ Coinvariants.ker ρ := by
  rintro _ ⟨v, rfl⟩
  exact cocycles₁_apply_mem_coinvariantsKer_of_mem_commutator ((freeCocycleEquiv ρ).symm v) hr

end Free

section Presented

variable {rels : Set (FreeGroup X)} (ρ : Representation k (PresentedGroup rels) V)

/-- Evaluation of a one-cocycle of a presented group at the generators. -/
noncomputable def cocyclesEvalOf : cocycles₁ (Rep.of ρ) →ₗ[k] (X → V) where
  toFun f x := f (PresentedGroup.of x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem cocyclesEvalOf_apply (f : cocycles₁ (Rep.of ρ)) (x : X) :
    cocyclesEvalOf ρ f x = f (PresentedGroup.of x) := (rfl)

theorem cocyclesEvalOf_injective : Function.Injective (cocyclesEvalOf ρ) := fun f f' h ↦
  cocycles₁_ext_of_closure_eq_top (PresentedGroup.closure_range_of rels) <| by
    rintro _ ⟨x, rfl⟩
    exact congrFun h x

/-- **The one-cocycles of a finitely generated group are finite.** For a presented group with
finitely many generators and a finite module `V` over a Noetherian ring, `Z¹(⟨X | R⟩, V)` embeds
into `X → V` by evaluation at the generators. -/
instance [IsNoetherianRing k] [Finite X] [Module.Finite k V] :
    Module.Finite k (cocycles₁ (Rep.of ρ)) :=
  Module.Finite.of_injective (cocyclesEvalOf ρ) (cocyclesEvalOf_injective ρ)

/-- **The Fox map evaluates a cocycle of the presented group.** The Fox map of a word `w`, for
the representation pulled back to the free group, sends the generator values of a cocycle `f`
of `⟨X | R⟩` to the value of `f` at the image of `w`. -/
theorem foxMap_cocyclesEvalOf (f : cocycles₁ (Rep.of ρ)) (w : FreeGroup X) :
    foxMap (ρ.comp (PresentedGroup.mk rels)) w (cocyclesEvalOf ρ f) =
      f (PresentedGroup.mk rels w) := by
  have hf : (fun w ↦ f (PresentedGroup.mk rels w)) ∈
      cocycles₁ (Rep.of (ρ.comp (PresentedGroup.mk rels))) :=
    (mem_cocycles₁_iff _).2 fun w w' ↦ by
      simpa using cocycles₁_map_mul f (PresentedGroup.mk rels w) (PresentedGroup.mk rels w')
  exact congrFun (freeCocycle_comp_of (ρ.comp (PresentedGroup.mk rels)) ⟨_, hf⟩) w

/-- **One-cocycles on a presented group.** A tuple `v : X → V` is the tuple of values at the
generators of a one-cocycle of `⟨X | R⟩` exactly when the Fox map of every relator, for the
representation pulled back to the free group, vanishes at `v`. -/
theorem range_cocyclesEvalOf : LinearMap.range (cocyclesEvalOf ρ) =
    ⨅ r ∈ rels, LinearMap.ker (foxMap (ρ.comp (PresentedGroup.mk rels)) r) := by
  ext v
  simp only [LinearMap.mem_range, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · rintro ⟨f, rfl⟩ r hr
    rw [foxMap_cocyclesEvalOf, PresentedGroup.one_of_mem hr]
    exact cocycles₁_map_one (A := Rep.of ρ) f
  · intro hv
    set σ := ρ.comp (PresentedGroup.mk rels)
    have hlift : FreeGroup.lift (fun x ↦ freeAffineHom σ v (FreeGroup.of x)) = freeAffineHom σ v :=
      FreeGroup.ext_hom _ _ fun x ↦ FreeGroup.lift_apply_of
    -- The relators act trivially: their linear part is `ρ 1` and their translation part vanishes.
    have hrels (r) (hr : r ∈ rels) :
        FreeGroup.lift (fun x ↦ freeAffineHom σ v (FreeGroup.of x)) r = 1 := by
      rw [hlift]
      refine AffineEquiv.ext fun y ↦ ?_
      simp [σ, freeAffineHom_apply, ← foxMap_apply, hv r hr, PresentedGroup.one_of_mem hr]
    set φ := PresentedGroup.toGroup hrels
    have hφ (w : FreeGroup X) : φ (PresentedGroup.mk rels w) 0 = freeCocycle σ v w := by
      rw [freeCocycle, ← MonoidHom.comp_apply, ← hlift]
      exact DFunLike.congr_fun (DFunLike.congr_fun
        (FreeGroup.ext_hom _ _ fun x ↦ PresentedGroup.toGroup.of hrels) w) 0
    refine ⟨⟨fun g ↦ φ g 0, (mem_cocycles₁_iff _).2 fun g h ↦ ?_⟩, funext fun x ↦ ?_⟩
    · obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective rels g
      obtain ⟨w', rfl⟩ := PresentedGroup.mk_surjective rels h
      rw [← map_mul, hφ, hφ, hφ, freeCocycle_mul, Rep.of_ρ, MonoidHom.comp_apply]
    · exact (DFunLike.congr_fun (PresentedGroup.toGroup.of hrels) 0).trans (freeCocycle_of σ v x)

/-- **One-cocycles on a presented group are the tuples killed by the Fox maps of the
relators.** Evaluation at the generators identifies the one-cocycles of `⟨X | R⟩` with the
common kernel of the Fox maps `Representation.foxMap (ρ.comp (PresentedGroup.mk rels)) r`,
`r ∈ R`. -/
noncomputable def presentedCocyclesEquiv : cocycles₁ (Rep.of ρ) ≃ₗ[k]
    ↥(⨅ r ∈ rels, LinearMap.ker (foxMap (ρ.comp (PresentedGroup.mk rels)) r)) :=
  (LinearEquiv.ofInjective _ (cocyclesEvalOf_injective ρ)).trans
    (LinearEquiv.ofEq _ _ (range_cocyclesEvalOf ρ))

@[simp]
theorem coe_presentedCocyclesEquiv_apply (f : cocycles₁ (Rep.of ρ)) :
    (presentedCocyclesEquiv ρ f : X → V) = cocyclesEvalOf ρ f := (rfl)

end Presented

end Representation
