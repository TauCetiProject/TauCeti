/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Determinant

/-!
# Bases of the middle term of a short exact sequence, with arbitrary lifts

Let `0 → A → B → C → 0` be a short exact sequence of modules, given by an injective linear map
`f : A →ₗ[R] B` and a linear map `g : B →ₗ[R] C` with `Function.Exact f g`. A basis `a` of `A`,
a basis `c` of `C` and any family `s` of lifts of `c` through `g` combine into the basis
`Module.Basis.ofExactLift` of `B`, indexed by the sum of the two index types: it is `f ∘ a` on
the left summand and `s` on the right summand.

Unlike Mathlib's `ModuleCat.Basis.ofShortExact` and `Module.Basis.sumQuot`, which fix one choice
of lifts, the lifts here are arbitrary. This is what the bracket determinants `[a s / b]` of
Reidemeister torsion need: in a short exact sequence, the determinant of `ofExactLift a c s`
with respect to a basis of `B` changes by `a.det a' * c.det c'` when `a`, `c` are replaced by
`a'`, `c'`, and does not depend on the lifts at all (`Module.Basis.det_ofExactLift`), because the
transition matrix between two such bases is block upper triangular
(`Module.Basis.toMatrix_ofExactLift`).

## Main declarations

* `Module.Basis.ofExactLift`: the basis of `B` assembled from `a`, `c` and the lifts `s`.
* `Module.Basis.eq_ofExactLift`: every basis of `B` made of the image of `a` followed by lifts
  of `c` is of this form.
* `Module.Basis.eq_reindex_ofExactLift`: the same for a basis indexed by `Fin (m + n)`.
* `Module.Basis.ofExactLift_det_eq_mul`: the determinant with respect to such a basis of a family
  made of images of a family `x` of `A` and of lifts of a family `y` of `C` is
  `a.det x * c.det y`.
* `Module.Basis.ofExactLift_det_ofExactLift`: the determinant of one such basis with respect to
  another is `a.det a' * c.det c'`.
* `Module.Basis.det_ofExactLift`: the corresponding transformation law for the determinant with
  respect to an arbitrary basis of `B`.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1.
-/

public section

noncomputable section

namespace Module.Basis

variable {R A B C : Type*} [Semiring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C} {κ σ : Type*}
  (hf : Function.Injective f) (hfg : Function.Exact f g)

/-- The splitting `B ≃ₗ[R] A × C` of a short exact sequence determined by lifts `s` of a basis of
`C`. -/
private def exactLiftEquiv (c : Basis σ R C) (s : σ → B) (hs : ∀ j, g (s j) = c j) :
    B ≃ₗ[R] A × C :=
  (hfg.splitSurjectiveEquiv hf ⟨c.constr ℕ s, c.ext fun j ↦ by simp [hs]⟩).1

variable {hf hfg}

private theorem exactLiftEquiv_apply (c : Basis σ R C) (s : σ → B) (hs : ∀ j, g (s j) = c j)
    (x : A) : exactLiftEquiv hf hfg c s hs (f x) = (x, 0) := by
  have := congrArg (fun φ : A →ₗ[R] B ↦ exactLiftEquiv hf hfg c s hs (φ x))
    (hfg.splitSurjectiveEquiv hf ⟨c.constr ℕ s, c.ext fun j ↦ by simp [hs]⟩).2.1
  simpa [exactLiftEquiv] using this

private theorem exactLiftEquiv_apply_snd (c : Basis σ R C) (s : σ → B)
    (hs : ∀ j, g (s j) = c j) (y : B) : (exactLiftEquiv hf hfg c s hs y).2 = g y := by
  have := congrArg (fun φ : B →ₗ[R] C ↦ φ y)
    (hfg.splitSurjectiveEquiv hf ⟨c.constr ℕ s, c.ext fun j ↦ by simp [hs]⟩).2.2
  simpa [exactLiftEquiv] using this.symm

private theorem exactLiftEquiv_symm_inr (c : Basis σ R C) (s : σ → B)
    (hs : ∀ j, g (s j) = c j) (j : σ) : (exactLiftEquiv hf hfg c s hs).symm (0, c j) = s j := by
  let l : { l : C →ₗ[R] B // g ∘ₗ l = .id } := ⟨c.constr ℕ s, c.ext fun j ↦ by simp [hs]⟩
  -- The inverse of `splitSurjectiveEquiv` sends a splitting `e` to the section `e.symm ∘ₗ inr`,
  -- so the first step holds by definition.
  calc (exactLiftEquiv hf hfg c s hs).symm (0, c j)
      = ((hfg.splitSurjectiveEquiv hf).symm (hfg.splitSurjectiveEquiv hf l)).1 (c j) := rfl
    _ = s j := by rw [Equiv.symm_apply_apply, constr_basis]

variable (hf hfg)

/-- In a short exact sequence `0 → A → B → C → 0`, a basis `a` of `A`, a basis `c` of `C` and
lifts `s` of the vectors of `c` through `B → C` together form a basis of `B`, indexed by
`κ ⊕ σ`: the image of `a` on the left summand and the lifts `s` on the right summand. -/
def ofExactLift (a : Basis κ R A) (c : Basis σ R C) (s : σ → B) (hs : ∀ j, g (s j) = c j) :
    Basis (κ ⊕ σ) R B :=
  (a.prod c).map (exactLiftEquiv hf hfg c s hs).symm

variable (a : Basis κ R A) (c : Basis σ R C) (s : σ → B) (hs : ∀ j, g (s j) = c j)

/-- On the left summand, `ofExactLift` is the image of the basis `a` of `A`. -/
@[simp]
theorem ofExactLift_inl (i : κ) : ofExactLift hf hfg a c s hs (Sum.inl i) = f (a i) := by
  rw [ofExactLift, map_apply, LinearEquiv.symm_apply_eq, exactLiftEquiv_apply]
  ext <;> simp

/-- On the right summand, `ofExactLift` is the chosen family `s` of lifts. -/
@[simp]
theorem ofExactLift_inr (j : σ) : ofExactLift hf hfg a c s hs (Sum.inr j) = s j := by
  rw [ofExactLift, map_apply, ← exactLiftEquiv_symm_inr (hf := hf) (hfg := hfg) c s hs j]
  congr 1
  ext <;> simp

/-- The coordinates of a vector of `B` on the right summand of `ofExactLift` are the coordinates
of its image in `C`. -/
@[simp]
theorem ofExactLift_repr_inr (y : B) (j : σ) :
    (ofExactLift hf hfg a c s hs).repr y (Sum.inr j) = c.repr (g y) j := by
  simp [ofExactLift, prod_repr_inr, exactLiftEquiv_apply_snd]

/-- The coordinates of a vector of `A`, viewed in `B`, on the left summand of `ofExactLift` are
its coordinates in `a`. -/
@[simp]
theorem ofExactLift_repr_apply_inl (x : A) (i : κ) :
    (ofExactLift hf hfg a c s hs).repr (f x) (Sum.inl i) = a.repr x i := by
  simp [ofExactLift, prod_repr_inl, exactLiftEquiv_apply]

/-- A basis of `B` indexed by `κ ⊕ σ` that is the image of the basis `a` of `A` on the left
summand, and whose vectors on the right summand lift the basis `c` of `C`, is the basis
`ofExactLift` with these lifts. -/
theorem eq_ofExactLift (b : Basis (κ ⊕ σ) R B) (hb : ∀ i, b (.inl i) = f (a i))
    (hb' : ∀ j, g (b (.inr j)) = c j) :
    b = ofExactLift hf hfg a c (fun j ↦ b (.inr j)) hb' :=
  eq_of_apply_eq fun | .inl i => by simp [hb] | .inr j => by simp

/-- A basis of `B` indexed by `Fin (m + n)` that is the image of the basis `a` of `A` on the first
`m` indices, and whose last `n` vectors lift the basis `c` of `C`, is the basis `ofExactLift`
with these lifts, reindexed by `finSumFinEquiv`. -/
theorem eq_reindex_ofExactLift {m n : ℕ} (a : Basis (Fin m) R A) (c : Basis (Fin n) R C)
    (b : Basis (Fin (m + n)) R B) (hb : ∀ i, b (Fin.castAdd n i) = f (a i))
    (hb' : ∀ j, g (b (Fin.natAdd m j)) = c j) :
    b = (ofExactLift hf hfg a c (fun j ↦ b (Fin.natAdd m j)) hb').reindex finSumFinEquiv :=
  calc b = (b.reindex finSumFinEquiv.symm).reindex finSumFinEquiv :=
        eq_of_apply_eq fun _ ↦ by simp
    _ = _ := by
      rw [eq_ofExactLift hf hfg a c (b.reindex finSumFinEquiv.symm) (by simp [hb])
        fun j ↦ by simpa using hb' j]
      congr 2
      ext j
      simp

section CommSemiring

variable {R A B C : Type*} [CommSemiring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C} {κ σ : Type*}
  (hf : Function.Injective f) (hfg : Function.Exact f g)
  (a a' : Basis κ R A) (c c' : Basis σ R C) (s s' : σ → B)
  (hs : ∀ j, g (s j) = c j) (hs' : ∀ j, g (s' j) = c' j)

/-- The transition matrix between two bases of the form `ofExactLift` is block upper triangular,
with diagonal blocks the transition matrices of the bases of `A` and of `C`. -/
theorem toMatrix_ofExactLift :
    (ofExactLift hf hfg a c s hs).toMatrix (ofExactLift hf hfg a' c' s' hs') =
      Matrix.fromBlocks (a.toMatrix a')
        (Matrix.of fun i j ↦ (ofExactLift hf hfg a c s hs).repr (s' j) (Sum.inl i)) 0
        (c.toMatrix c') := by
  ext (i | j) (k | l)
  · simp [toMatrix_apply]
  · simp [toMatrix_apply]
  · simp [toMatrix_apply, hfg.apply_apply_eq_zero]
  · simp [toMatrix_apply, hs']

end CommSemiring

section CommRing

variable {R A B C : Type*} [CommRing R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C} {κ σ : Type*}
  (hf : Function.Injective f) (hfg : Function.Exact f g)
  (a a' : Basis κ R A) (c c' : Basis σ R C) (s s' : σ → B)
  (hs : ∀ j, g (s j) = c j) (hs' : ∀ j, g (s' j) = c' j)
  [Fintype κ] [Fintype σ] [DecidableEq κ] [DecidableEq σ]

/-- The determinant with respect to `ofExactLift a c s` of a family `v` of `B`, made of the
images of a family `x` of `A` followed by lifts of a family `y` of `C`, is `a.det x * c.det y`:
the matrix of `v` is block upper triangular. -/
theorem ofExactLift_det_eq_mul (x : κ → A) (y : σ → C) (v : κ ⊕ σ → B)
    (hx : ∀ i, v (.inl i) = f (x i)) (hy : ∀ j, g (v (.inr j)) = y j) :
    (ofExactLift hf hfg a c s hs).det v = a.det x * c.det y := by
  have h : (ofExactLift hf hfg a c s hs).toMatrix v = Matrix.fromBlocks (a.toMatrix x)
      (Matrix.of fun i j ↦ (ofExactLift hf hfg a c s hs).repr (v (.inr j)) (.inl i)) 0
      (c.toMatrix y) := by
    ext (i | j) (k | l) <;> simp [toMatrix_apply, hx, hy, hfg.apply_apply_eq_zero]
  rw [det_apply, h, Matrix.det_fromBlocks_zero₂₁, det_apply, det_apply]

/-- The determinant of one basis of the form `ofExactLift` with respect to another is the
product of the determinants of the bases of `A` and of `C`; in particular it does not depend on
the lifts. -/
theorem ofExactLift_det_ofExactLift :
    (ofExactLift hf hfg a c s hs).det (ofExactLift hf hfg a' c' s' hs') = a.det a' * c.det c' :=
  ofExactLift_det_eq_mul hf hfg a c s hs a' c' _ (by simp) (by simp [hs'])

/-- Replacing the bases `a`, `c` and the lifts `s` in `ofExactLift` multiplies its determinant
with respect to any basis `b` of `B` by `a.det a' * c.det c'`. In particular the determinant
does not depend on the choice of lifts. -/
theorem det_ofExactLift (b : Basis (κ ⊕ σ) R B) :
    b.det (ofExactLift hf hfg a' c' s' hs') =
      b.det (ofExactLift hf hfg a c s hs) * (a.det a' * c.det c') := by
  rw [← ofExactLift_det_ofExactLift hf hfg a a' c c' s s' hs hs', det_mul_det]

end CommRing

end Module.Basis
