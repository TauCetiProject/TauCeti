/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero

/-!
# The projection monoid and `K₀` of a product

A matrix over `R × S` is a pair of matrices over `R` and over `S`, and a matrix projection over
`R × S` is the orthogonal sum of its two components, embedded through `R → R × S` and
`S → R × S`. Since orthogonal projections have additive classes
(`TauCeti.ProjectionMonoid.mk_add_of_mul_eq_zero`), the projections `R × S → R` and
`R × S → S` induce isomorphisms `V(R × S) ≃+ V(R) × V(S)`
(`TauCeti.ProjectionMonoid.prodEquiv`) and `K₀(R × S) ≃+ K₀(R) × K₀(S)`
(`TauCeti.ProjectionKZero.prodEquiv`), with inverses induced by the inclusions.

## Main statements

* `TauCeti.ProjectionMonoid.mk_add_of_mul_eq_zero`: `[p + q] = [p] + [q]` for orthogonal
  projections `p` and `q`.
* `TauCeti.ProjectionMonoid.prodEquiv`: `V(R × S) ≃+ V(R) × V(S)`.
* `TauCeti.ProjectionKZero.prodEquiv`: `K₀(R × S) ≃+ K₀(R) × K₀(S)`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §5.2.
-/

public section

open Matrix Algebra

namespace TauCeti

variable {R S : Type*} [NonUnitalSemiring R] [StarRing R] [NonUnitalSemiring S] [StarRing S]

namespace ProjectionMonoid

variable {m : Type*} [Fintype m]

/-- **Orthogonal sums.** The class of the sum of orthogonal projections `p` and `q` is the sum of
their classes. -/
theorem mk_add_of_mul_eq_zero {p q : Matrix m m R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p * q = 0) :
    mk (p + q) (hp.add hq hpq) = mk p hp + mk q hq := by
  rw [← mk_fromBlocks, mk_eq_mk_iff]
  have h := (hp.isMurrayVonNeumannEquivalent_fromBlocks_zero (n := m)).add
    (hq.isMurrayVonNeumannEquivalent_zero_fromBlocks (n := m)) hpq
    (by rw [fromBlocks_multiply]; simp)
  simpa only [fromBlocks_add, add_zero, zero_add] using h

/-- If a star ring homomorphism vanishes, so does the homomorphism it induces on `V`. -/
theorem map_eq_zero_of_forall_eq_zero {f : R →⋆ₙ+* S} (hf : ∀ r, f r = 0)
    (x : ProjectionMonoid R) : map f x = 0 := by
  induction x using ind with
  | mk _ p hp =>
    rw [map_mk, mk_eq_zero_iff]
    ext i j
    exact hf _

variable (R S) in
/-- The first projection `R × S → R` as a star ring homomorphism. -/
noncomputable abbrev fstHom : R × S →⋆ₙ+* R :=
  NonUnitalStarRingHom.ofClass (NonUnitalStarAlgHom.fst ℕ R S)

variable (R S) in
/-- The second projection `R × S → S` as a star ring homomorphism. -/
noncomputable abbrev sndHom : R × S →⋆ₙ+* S :=
  NonUnitalStarRingHom.ofClass (NonUnitalStarAlgHom.snd ℕ R S)

variable (R S) in
/-- The first inclusion `R → R × S` as a star ring homomorphism. -/
noncomputable abbrev inlHom : R →⋆ₙ+* R × S :=
  NonUnitalStarRingHom.ofClass (NonUnitalStarAlgHom.inl ℕ R S)

variable (R S) in
/-- The second inclusion `S → R × S` as a star ring homomorphism. -/
noncomputable abbrev inrHom : S →⋆ₙ+* R × S :=
  NonUnitalStarRingHom.ofClass (NonUnitalStarAlgHom.inr ℕ R S)

/-- A matrix projection over `R × S` is the class of the sum of its two components. -/
theorem map_inlHom_map_fstHom_add (x : ProjectionMonoid (R × S)) :
    map (inlHom R S) (map (fstHom R S) x) + map (inrHom R S) (map (sndHom R S) x) = x := by
  induction x using ind with
  | mk _ p hp =>
    simp only [map_mk, Matrix.map_map]
    rw [← mk_add_of_mul_eq_zero _ _ (by
      ext i j <;> simp [Matrix.mul_apply])]
    congr 1
    ext i j <;> simp

variable (R S) in
/-- **The projection monoid of a product**: `V(R × S) ≃+ V(R) × V(S)`, induced by the two
projections, with inverse induced by the two inclusions. -/
noncomputable def prodEquiv : ProjectionMonoid (R × S) ≃+ ProjectionMonoid R × ProjectionMonoid S
    where
  toFun x := (map (fstHom R S) x, map (sndHom R S) x)
  invFun y := map (inlHom R S) y.1 + map (inrHom R S) y.2
  left_inv := map_inlHom_map_fstHom_add
  right_inv y := by
    obtain ⟨x, y⟩ := y
    have h₁ : (fstHom R S).comp (inlHom R S) = NonUnitalStarRingHom.id R := by ext; simp
    have h₂ : (sndHom R S).comp (inrHom R S) = NonUnitalStarRingHom.id S := by ext; simp
    have h₃ : map ((fstHom R S).comp (inrHom R S)) y = 0 :=
      map_eq_zero_of_forall_eq_zero (fun _ ↦ by simp) y
    have h₄ : map ((sndHom R S).comp (inlHom R S)) x = 0 :=
      map_eq_zero_of_forall_eq_zero (fun _ ↦ by simp) x
    simp only [map_add, ← AddMonoidHom.comp_apply, ← map_comp, h₁, h₂, h₃, h₄, map_id,
      AddMonoidHom.id_apply, add_zero, zero_add]
  map_add' x y := by simp

/-- The class in `V(R) × V(S)` of a matrix projection over `R × S` is the pair of the classes of
its components. -/
@[simp]
theorem prodEquiv_mk {p : Matrix m m (R × S)} (hp : IsStarProjection p) :
    prodEquiv R S (mk p hp) =
      (mk (p.map Prod.fst) (hp.matrix_map (fstHom R S)),
        mk (p.map Prod.snd) (hp.matrix_map (sndHom R S))) :=
  Prod.ext (map_mk _ hp) (map_mk _ hp)

end ProjectionMonoid

namespace ProjectionKZero

open ProjectionMonoid

/-- If a star ring homomorphism vanishes, so does the homomorphism it induces on `K₀`. -/
theorem map_eq_zero_of_forall_eq_zero {f : R →⋆ₙ+* S} (hf : ∀ r, f r = 0) : map f = 0 :=
  GrothendieckAddGroup.addHom_ext fun x ↦ by
    rw [map_of, ProjectionMonoid.map_eq_zero_of_forall_eq_zero hf, map_zero,
      AddMonoidHom.zero_apply]

variable (R S) in
/-- **`K₀` of a product**: `K₀(R × S) ≃+ K₀(R) × K₀(S)`, induced by the two projections, with
inverse induced by the two inclusions. -/
noncomputable def prodEquiv : ProjectionKZero (R × S) ≃+ ProjectionKZero R × ProjectionKZero S :=
  AddMonoidHom.toAddEquiv ((map (fstHom R S)).prod (map (sndHom R S)))
    ((map (inlHom R S)).coprod (map (inrHom R S)))
    (GrothendieckAddGroup.addHom_ext fun x ↦ by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.prod_apply, AddMonoidHom.coprod_apply, map_of,
        map_of, map_of, map_of, ← map_add, map_inlHom_map_fstHom_add, AddMonoidHom.id_apply])
    (by
      have h₁ : (fstHom R S).comp (inlHom R S) = NonUnitalStarRingHom.id R := by ext; simp
      have h₂ : (sndHom R S).comp (inrHom R S) = NonUnitalStarRingHom.id S := by ext; simp
      have h₃ : map ((fstHom R S).comp (inrHom R S)) = 0 :=
        map_eq_zero_of_forall_eq_zero fun _ ↦ by simp
      have h₄ : map ((sndHom R S).comp (inlHom R S)) = 0 :=
        map_eq_zero_of_forall_eq_zero fun _ ↦ by simp
      refine AddMonoidHom.ext fun y ↦ ?_
      obtain ⟨x, y⟩ := y
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.prod_apply, AddMonoidHom.coprod_apply,
        map_add, ← AddMonoidHom.comp_apply (map (fstHom R S)), ← AddMonoidHom.comp_apply
        (map (sndHom R S)), ← map_comp, h₁, h₂, h₃, h₄, map_id, AddMonoidHom.id_apply,
        AddMonoidHom.zero_apply]
      rw [Prod.mk_add_mk, add_zero, zero_add])

/-- The isomorphism `K₀(R × S) ≃+ K₀(R) × K₀(S)` is induced by the two projections. -/
theorem prodEquiv_apply (x : ProjectionKZero (R × S)) :
    prodEquiv R S x = (map (fstHom R S) x, map (sndHom R S) x) :=
  (rfl)

end ProjectionKZero

end TauCeti
