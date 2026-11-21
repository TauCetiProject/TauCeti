/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Tactic.Abel
import TauCeti.RepresentationTheory.Coinvariants

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
For a presented group `G = ⟨X | R⟩` and a representation `ρ` of `G`, evaluation at the generators
identifies `Z¹(G, V)` with the common kernel of the Fox maps of the relators
(`Representation.presentedCocyclesEquiv`): a cocycle on `F(X)` for the pulled-back
representation descends to `G` exactly when it vanishes on the relators. This is the standard
computation of `Z¹` from a presentation, used for surface groups in
`TauCeti.RepresentationTheory.Homological.GroupCohomology.SurfaceGroup`.

The Fox maps satisfy the product rule `∂(r s) = ∂r + r ∂s` (`Representation.foxMap_mul`). The
value of a one-cocycle at a commutator `a⁻¹ b⁻¹ a b` is given by the Fox derivatives of the
commutator (`groupCohomology.cocycles₁_apply_inv_mul_inv_mul_mul`). Modulo the coinvariant kernel
`Representation.Coinvariants.ker ρ`, a one-cocycle is a homomorphism to the coinvariants, so it
takes values in the coinvariant kernel on the commutator subgroup
(`groupCohomology.cocycles₁_apply_mem_coinvariantsKer_of_mem_commutator`); hence the Fox map of
a product of commutators lands in the coinvariant kernel
(`Representation.range_foxMap_le_coinvariantsKer`).

## References

* R. H. Fox, *Free differential calculus. I. Derivation in the free group ring*, Annals of
  Mathematics 57 (1953), 547–560.
* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer, 1982,
  Chapter IV, §2 (derivations and cocycles).
-/

public section

open CategoryTheory groupCohomology

universe u w

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G] {A : Rep.{w} k G}

/-- **A one-cocycle is determined by its values on a generating set.** -/
theorem cocycles₁_ext_of_closure_eq_top {s : Set G} (hs : Subgroup.closure s = ⊤)
    {f f' : cocycles₁ A} (h : ∀ g ∈ s, f g = f' g) : f = f' := by
  ext g
  induction hs.ge (Subgroup.mem_top g) using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => simp
  | mul g g' _ _ hg hg' =>
    rw [(mem_cocycles₁_iff (f : G → A)).1 f.property,
      (mem_cocycles₁_iff (f' : G → A)).1 f'.property, hg, hg']
  | inv g _ hg =>
    have hf := cocycles₁_map_inv f g
    have hf' := cocycles₁_map_inv f' g
    rw [hg, ← hf'] at hf
    have := congrArg (A.ρ g⁻¹) hf
    rwa [Representation.inv_self_apply, Representation.inv_self_apply] at this

/-- A one-cocycle vanishing at every element of a list vanishes at its product. -/
theorem cocycles₁_list_prod_eq_zero (f : cocycles₁ A) {l : List G} (hl : ∀ x ∈ l, f x = 0) :
    f l.prod = 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.prod_cons, (mem_cocycles₁_iff (f : G → A)).1 f.property,
      ih fun y hy ↦ hl y (List.mem_cons_of_mem x hy), hl x List.mem_cons_self, map_zero, add_zero]

/-- **The value of a one-cocycle at a commutator.** For the commutator `a⁻¹ * b⁻¹ * a * b`, the
cocycle identity gives
`f (a⁻¹ b⁻¹ a b) = (ρ (a⁻¹ b⁻¹) - ρ a⁻¹) (f a) + (ρ (a⁻¹ b⁻¹ a) - ρ (a⁻¹ b⁻¹)) (f b)`, the Fox
derivatives of the commutator applied to the values at `a` and `b`. -/
theorem cocycles₁_apply_inv_mul_inv_mul_mul (f : cocycles₁ A) (a b : G) :
    f (a⁻¹ * b⁻¹ * a * b) = A.ρ (a⁻¹ * b⁻¹) (f a) - A.ρ a⁻¹ (f a) +
      (A.ρ (a⁻¹ * b⁻¹ * a) (f b) - A.ρ (a⁻¹ * b⁻¹) (f b)) := by
  have hmul := (mem_cocycles₁_iff (f : G → A)).1 f.property
  have hinv (c : G) : f c⁻¹ = -A.ρ c⁻¹ (f c) := by
    have := congrArg (A.ρ c⁻¹) (cocycles₁_map_inv f c)
    rwa [Representation.inv_self_apply, map_neg] at this
  rw [hmul, hmul, hmul, hinv a, hinv b]
  simp only [map_neg, map_mul, mul_apply_eq_comp]
  abel

/-- **A one-cocycle takes values in the coinvariant kernel on the commutator subgroup.** Modulo
the coinvariant kernel the cocycle identity reads `f (g * h) = f h + f g`, so `f` becomes a
homomorphism to an abelian group, which kills commutators. -/
theorem cocycles₁_apply_mem_coinvariantsKer_of_mem_commutator (f : cocycles₁ A) {g : G}
    (hg : g ∈ commutator G) : f g ∈ Representation.Coinvariants.ker A.ρ := by
  let φ : G →* Multiplicative (Representation.Coinvariants A.ρ) :=
    { toFun g := .ofAdd (Representation.Coinvariants.mk A.ρ (f g))
      map_one' := by simp
      map_mul' g h := by
        rw [(mem_cocycles₁_iff (f : G → A)).1 f.property]
        simp [← ofAdd_add, add_comm] }
  have hle : commutator G ≤ φ.ker := Group.Abelianization.commutator_le_ker φ
  have := hle hg
  rw [MonoidHom.mem_ker] at this
  exact (Representation.Coinvariants.mk_eq_zero _).1 (by simpa [φ] using this)

end groupCohomology

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
  rw [freeCocycle, map_mul, AffineEquiv.coe_mul, Function.comp_apply, freeAffineHom_apply]
  rfl

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

end Free

section Presented

variable {rels : Set (FreeGroup X)} (ρ : Representation k (PresentedGroup rels) V)

/-- **The Fox map of a word `r`**: the value at `r` of the free cocycle, for the representation
pulled back to the free group, as a linear function of its values on the generators. In Fox's
free differential calculus it is `v ↦ ∑ₓ ρ(∂r/∂x) (v x)`. -/
noncomputable def foxMap (r : FreeGroup X) : (X → V) →ₗ[k] V :=
  (LinearMap.proj r ∘ₗ (cocycles₁ (Rep.of (ρ.comp (PresentedGroup.mk rels)))).subtype) ∘ₗ
    (freeCocycleEquiv (ρ.comp (PresentedGroup.mk rels))).symm.toLinearMap

theorem foxMap_apply (r : FreeGroup X) (v : X → V) :
    foxMap ρ r v = freeCocycle (ρ.comp (PresentedGroup.mk rels)) v r := (rfl)

/-- The Fox map of a generator is evaluation at that generator. -/
@[simp]
theorem foxMap_of (x : X) (v : X → V) : foxMap ρ (FreeGroup.of x) v = v x :=
  freeCocycle_of _ v x

/-- **The product rule for Fox maps**, `∂(r s) = ∂r + r ∂s`. -/
theorem foxMap_mul (r s : FreeGroup X) (v : X → V) :
    foxMap ρ (r * s) v = ρ (PresentedGroup.mk rels r) (foxMap ρ s v) + foxMap ρ r v :=
  freeCocycle_mul _ v r s

/-- **The Fox map of a product of commutators lands in the coinvariant kernel.** If the word `r`
lies in the commutator subgroup of the free group, every value of its Fox map lies in the span of
the `ρ g y - y`. -/
theorem range_foxMap_le_coinvariantsKer {r : FreeGroup X} (hr : r ∈ commutator (FreeGroup X)) :
    LinearMap.range (foxMap ρ r) ≤ Coinvariants.ker ρ := by
  rintro _ ⟨v, rfl⟩
  have := cocycles₁_apply_mem_coinvariantsKer_of_mem_commutator
    ((freeCocycleEquiv (ρ.comp (PresentedGroup.mk rels))).symm v) hr
  rwa [Rep.of_ρ, coinvariantsKer_comp_of_surjective _ _ (PresentedGroup.mk_surjective rels)] at this

/-- Evaluation of a one-cocycle of a presented group at the generators. -/
noncomputable def cocyclesEvalOf : cocycles₁ (Rep.of ρ) →ₗ[k] (X → V) where
  toFun f x := f (PresentedGroup.of x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem cocyclesEvalOf_apply (f : cocycles₁ (Rep.of ρ)) (x : X) :
    cocyclesEvalOf ρ f x = f (PresentedGroup.of x) := (rfl)

theorem injective_cocyclesEvalOf : Function.Injective (cocyclesEvalOf ρ) := fun f f' h ↦
  cocycles₁_ext_of_closure_eq_top (PresentedGroup.closure_range_of rels) <| by
    rintro _ ⟨x, rfl⟩
    exact congrFun h x

/-- The free cocycle of the generator values of a cocycle `f` of the presented group is `f`
composed with the quotient map. -/
private theorem freeCocycle_comp_mk_cocyclesEvalOf (f : cocycles₁ (Rep.of ρ)) :
    freeCocycle (ρ.comp (PresentedGroup.mk rels)) (cocyclesEvalOf ρ f) =
      fun w ↦ f (PresentedGroup.mk rels w) := by
  have hf : (fun w ↦ f (PresentedGroup.mk rels w)) ∈
      cocycles₁ (Rep.of (ρ.comp (PresentedGroup.mk rels))) :=
    (mem_cocycles₁_iff _).2 fun w w' ↦ by
      simpa using (mem_cocycles₁_iff (f : PresentedGroup rels → V)).1 f.property
        (PresentedGroup.mk rels w) (PresentedGroup.mk rels w')
  exact freeCocycle_comp_of (ρ.comp (PresentedGroup.mk rels)) ⟨_, hf⟩

/-- A free cocycle vanishing on the relators vanishes on the kernel of the quotient map. -/
private theorem freeCocycle_eq_zero_of_mk_eq_one {v : X → V}
    (hv : ∀ r ∈ rels, foxMap ρ r v = 0) {n : FreeGroup X} (hn : PresentedGroup.mk rels n = 1) :
    freeCocycle (ρ.comp (PresentedGroup.mk rels)) v n = 0 := by
  let f := (freeCocycleEquiv (ρ.comp (PresentedGroup.mk rels))).symm v
  have hmul (a b : FreeGroup X) : f (a * b) = ρ (PresentedGroup.mk rels a) (f b) + f a :=
    (mem_cocycles₁_iff (f : FreeGroup X → V)).1 f.property a b
  have hinv (a : FreeGroup X) : ρ (PresentedGroup.mk rels a) (f a⁻¹) = -f a :=
    cocycles₁_map_inv f a
  let N : Subgroup (FreeGroup X) :=
    { carrier := {n | PresentedGroup.mk rels n = 1 ∧ f n = 0}
      one_mem' := ⟨map_one _, cocycles₁_map_one f⟩
      mul_mem' := fun {a b} ha hb ↦ ⟨by simp [ha.1, hb.1], by
        simp only [hmul, hb.2, ha.2, map_zero, zero_add]⟩
      inv_mem' := fun {a} ha ↦ ⟨by simp [ha.1], by
        have := hinv a
        rw [ha.1, map_one, one_apply_eq_self, ha.2, neg_zero] at this
        exact this⟩ }
  have hN : N.Normal := ⟨fun a ha b ↦ ⟨by simp [ha.1], by
    change f (b * a * b⁻¹) = 0
    rw [hmul, hmul, ha.2, map_zero, zero_add]
    simp only [map_mul, ha.1, mul_one, hinv, neg_add_cancel]⟩⟩
  have hle : Subgroup.normalClosure rels ≤ N :=
    Subgroup.normalClosure_le_normal fun r hr ↦ ⟨PresentedGroup.one_of_mem hr, hv r hr⟩
  exact (hle (PresentedGroup.mk_eq_one_iff.1 hn)).2

/-- A free cocycle vanishing on the relators is constant on the fibres of the quotient map. -/
private theorem freeCocycle_eq_of_mk_eq {v : X → V} (hv : ∀ r ∈ rels, foxMap ρ r v = 0)
    {w w' : FreeGroup X} (h : PresentedGroup.mk rels w = PresentedGroup.mk rels w') :
    freeCocycle (ρ.comp (PresentedGroup.mk rels)) v w =
      freeCocycle (ρ.comp (PresentedGroup.mk rels)) v w' := by
  have hn : PresentedGroup.mk rels (w⁻¹ * w') = 1 := by simp [h]
  rw [← mul_inv_cancel_left w w', freeCocycle_mul,
    freeCocycle_eq_zero_of_mk_eq_one ρ hv hn, map_zero, zero_add]

/-- **One-cocycles on a presented group.** A tuple `v : X → V` is the tuple of values at the
generators of a one-cocycle of `⟨X | R⟩` exactly when the Fox map of every relator vanishes
at `v`. -/
theorem range_cocyclesEvalOf :
    LinearMap.range (cocyclesEvalOf ρ) = ⨅ r ∈ rels, LinearMap.ker (foxMap ρ r) := by
  ext v
  simp only [LinearMap.mem_range, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · rintro ⟨f, rfl⟩ r hr
    rw [foxMap_apply, freeCocycle_comp_mk_cocyclesEvalOf]
    simp only [PresentedGroup.one_of_mem hr]
    exact cocycles₁_map_one (A := Rep.of ρ) f
  · intro hv
    set σ := ρ.comp (PresentedGroup.mk rels)
    have hs := Function.surjInv_eq (PresentedGroup.mk_surjective rels)
    have hc (w : FreeGroup X) :
        freeCocycle σ v (Function.surjInv (PresentedGroup.mk_surjective rels)
          (PresentedGroup.mk rels w)) = freeCocycle σ v w :=
      freeCocycle_eq_of_mk_eq ρ hv (hs _)
    refine ⟨⟨fun g ↦ freeCocycle σ v (Function.surjInv (PresentedGroup.mk_surjective rels) g),
      (mem_cocycles₁_iff _).2 fun g h ↦ ?_⟩, ?_⟩
    · obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective rels g
      obtain ⟨w', rfl⟩ := PresentedGroup.mk_surjective rels h
      rw [← map_mul, hc, hc, hc, freeCocycle_mul]
      rfl
    · funext x
      exact (hc (FreeGroup.of x)).trans (freeCocycle_of σ v x)

/-- **One-cocycles on a presented group are the tuples killed by the Fox maps of the
relators.** Evaluation at the generators identifies the one-cocycles of `⟨X | R⟩` with the
common kernel of the Fox maps `Representation.foxMap ρ r`, `r ∈ R`. -/
noncomputable def presentedCocyclesEquiv :
    cocycles₁ (Rep.of ρ) ≃ₗ[k] ↥(⨅ r ∈ rels, LinearMap.ker (foxMap ρ r)) :=
  (LinearEquiv.ofInjective _ (injective_cocyclesEvalOf ρ)).trans
    (LinearEquiv.ofEq _ _ (range_cocyclesEvalOf ρ))

@[simp]
theorem coe_presentedCocyclesEquiv_apply (f : cocycles₁ (Rep.of ρ)) :
    (presentedCocyclesEquiv ρ f : X → V) = cocyclesEvalOf ρ f := (rfl)

end Presented

end Representation
