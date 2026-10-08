/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra

/-!
# Transport of A-infinity algebras along linear maps

An `A∞` structure on a graded module `A` transports along any linear equivalence `e : A ≃ B`:
the target is graded by the images of the pieces of `A`, as in `TauCeti.InternalGrading.map`, and
its operations are `mₙ(b₁, …, bₙ) = e (mₙ(e⁻¹ b₁, …, e⁻¹ bₙ))`.  The Stasheff identities
transport because they are natural in linear maps intertwining the operations,
`TauCeti.AInfinity.map_stasheffSum`.

This is how an `A∞` structure given on one model of a graded module is moved to another, for
instance from an algebra `A` to the total module of morphisms of the one-object graded linear
quiver with endomorphisms `A`.

An `A∞` structure on `B` also pulls back along an injective linear map `f : A → B` which detects
the degree of elements of `A` and whose image is closed under every operation: the operations of
`A` are the unique ones which `f` intertwines with those of `B`.  This is a sub-`A∞` algebra, and
`f` is a strict `A∞` morphism.  For instance, the morphisms between the objects of a full
subcategory of an `A∞` category form a sub-`A∞` algebra of the total algebra of morphisms.

## Main definitions

* `TauCeti.AInfinityAlgebra.map`: the transport of an `A∞` algebra along a linear equivalence.
* `TauCeti.AInfinityAlgebra.comap`: the pullback of an `A∞` algebra along an injective linear map
  whose image is closed under the operations.

## Main results

* `TauCeti.AInfinityAlgebra.map_grading` and `TauCeti.AInfinityAlgebra.map_m_apply`: the grading
  and the operations of the transported algebra.
* `TauCeti.AInfinityAlgebra.comap_grading` and `TauCeti.AInfinityAlgebra.map_m_comap`: the
  grading of the pulled-back algebra, and the injective map intertwines the operations.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

universe uR uA uB

namespace TauCeti

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]

namespace AInfinityAlgebra

variable [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- The **transport** of an `A∞` algebra along a linear equivalence `e : A ≃ B`.  The degree-`p`
piece of `B` is the image of the degree-`p` piece of `A`, and the operations are
`mₙ(b₁, …, bₙ) = e (mₙ(e⁻¹ b₁, …, e⁻¹ bₙ))`. -/
noncomputable def map (𝒜 : AInfinityAlgebra R A) (e : A ≃ₗ[R] B) : AInfinityAlgebra R B :=
  ofStasheff (𝒜.grading.map e)
    (fun n ↦ e.toLinearMap.compMultilinearMap ((𝒜.m n).compLinearMap fun _ ↦ e.symm.toLinearMap))
    (by simp)
    (fun n hn ↦ MultilinearMap.isHomogeneous_def.2 fun d x hx ↦ by
      simpa using (𝒜.m_degree n hn).map_mem d (fun i ↦ e.symm (x i))
        fun i ↦ (InternalGrading.mem_map_piece_iff _ _ _ _).1 (hx i))
    _ (AInfinity.isSuspension_suspensionTaylor _ _)
    (fun n hn d x hx ↦ e.symm.injective <| by
      rw [← LinearEquiv.coe_coe, AInfinity.map_stasheffSum _ d x e.symm.toLinearMap 𝒜.m
        (fun k y ↦ by simp), map_zero]
      exact 𝒜.stasheff n hn d _ fun i hi ↦ (InternalGrading.mem_map_piece_iff _ _ _ _).1 (hx i hi))

section Map

variable (𝒜 : AInfinityAlgebra R A) (e : A ≃ₗ[R] B)

/-- The grading of a transported `A∞` algebra is the transported grading. -/
@[simp]
theorem map_grading : (𝒜.map e).grading = 𝒜.grading.map e := by
  rw [map, ofStasheff_grading]

/-- The operations of a transported `A∞` algebra are conjugated by the linear equivalence. -/
@[simp]
theorem map_m_apply (n : ℕ) (x : Fin n → B) :
    (𝒜.map e).m n x = e (𝒜.m n fun i ↦ e.symm (x i)) := by
  simp [map, ofStasheff_m]

end Map

section Comap

variable (ℬ : AInfinityAlgebra R B) (G : InternalGrading R A) (f : A →ₗ[R] B)
  (hf : Function.Injective f) (hG : ∀ (p : ℤ) (a : A), f a ∈ ℬ.grading.piece p ↔ a ∈ G.piece p)
  (hm : ∀ n, 0 < n → ∀ x : Fin n → A, ℬ.m n (fun i ↦ f (x i)) ∈ LinearMap.range f)

include hm in
/-- The image of `f` is closed under every operation of `ℬ`, including the zero nullary one. -/
private theorem m_mem_range (n : ℕ) (x : Fin n → A) :
    ℬ.m n (fun i ↦ f (x i)) ∈ LinearMap.range f := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [ℬ.m_zero, zero_apply]
    exact zero_mem _
  · exact hm n hn x

/-- The operations of the pullback: `mₙ(a₁, …, aₙ)` is the preimage under `f` of
`mₙ(f a₁, …, f aₙ)`. -/
private noncomputable def comapOperation (n : ℕ) : MultilinearMap R (fun _ : Fin n ↦ A) A :=
  (LinearEquiv.ofInjective f hf).symm.toLinearMap.compMultilinearMap
    (((ℬ.m n).compLinearMap fun _ ↦ f).codRestrict _ (m_mem_range ℬ f hm n))

private theorem apply_comapOperation (n : ℕ) (x : Fin n → A) :
    f (comapOperation ℬ f hf hm n x) = ℬ.m n fun i ↦ f (x i) :=
  LinearEquiv.ofInjective_symm_apply f _

/-- The **pullback** of an `A∞` algebra `ℬ` on `B` along an injective linear map `f : A → B`
whose image is closed under the operations of `ℬ` of positive arity, for a grading `G` of `A`
whose degree `f` detects.  The operation `mₙ(a₁, …, aₙ)` is the unique preimage under `f` of
`mₙ(f a₁, …, f aₙ)`, as recorded by `TauCeti.AInfinityAlgebra.map_m_comap`. -/
noncomputable def comap : AInfinityAlgebra R A :=
  ofStasheff G (comapOperation ℬ f hf hm)
    (MultilinearMap.ext fun x ↦ hf <| by
      rw [apply_comapOperation, ℬ.m_zero, zero_apply, zero_apply,
        map_zero])
    (fun n hn ↦ MultilinearMap.isHomogeneous_def.2 fun d x hx ↦ (hG _ _).1 <| by
      rw [apply_comapOperation]
      exact (ℬ.m_degree n hn).map_mem d (fun i ↦ f (x i)) fun i ↦ (hG _ _).2 (hx i))
    _ (AInfinity.isSuspension_suspensionTaylor _ _)
    (fun n hn d x hx ↦ hf <| by
      rw [AInfinity.map_stasheffSum _ d x f ℬ.m (apply_comapOperation ℬ f hf hm), map_zero]
      exact ℬ.stasheff n hn d _ fun i hi ↦ (hG _ _).2 (hx i hi))

/-- The grading of the pullback of an `A∞` algebra is the given grading. -/
@[simp]
theorem comap_grading : (ℬ.comap G f hf hG hm).grading = G := by
  rw [comap, ofStasheff_grading]

/-- **The injective map intertwines the operations** of the pullback with those of the
algebra. -/
@[simp]
theorem map_m_comap (n : ℕ) (x : Fin n → A) :
    f ((ℬ.comap G f hf hG hm).m n x) = ℬ.m n fun i ↦ f (x i) := by
  rw [comap, ofStasheff_m, apply_comapOperation]

/-- The pullback of an `A∞` algebra is the unique `A∞` structure on `A` with grading `G` whose
operations the injective map intertwines with those of the algebra. -/
theorem eq_comap {ℬ' : AInfinityAlgebra R A} (hG' : ℬ'.grading = G)
    (hm' : ∀ n, 0 < n → ∀ x : Fin n → A, f (ℬ'.m n x) = ℬ.m n fun i ↦ f (x i)) :
    ℬ' = ℬ.comap G f hf hG hm := by
  refine ext (by rw [hG', comap_grading]) <| funext fun n ↦ ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [ℬ'.m_zero, AInfinityAlgebra.m_zero]
  · exact MultilinearMap.ext fun x ↦ hf (by rw [hm' n hn, map_m_comap])


end Comap

end AInfinityAlgebra

end TauCeti
