/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.K2
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Steinberg groups and `K₂` of a product of rings

For rings `R` and `S`, the Steinberg group of the product ring splits as a product,
`St_ι(R × S) ≃* St_ι(R) × St_ι(S)`, as soon as every pair of distinct indices admits a third index
distinct from both. The two components are induced by the projections `R × S → R` and
`R × S → S`. The inverse sends `(y, z)` to `inl y * inr z`, where `inl` and `inr` send `x_{ij}(a)`
to `x_{ij}(a, 0)` and `x_{ij}(b)` to `x_{ij}(0, b)`. The point is that these two images commute.
For index pairs that are not opposite this is a defining relation, because `(a, 0) * (0, b) = 0`.
For an opposite pair one writes `x_{ij}(a, 0) = ⁅x_{ik}(a, 0), x_{kj}(1, 0)⁆` with a third
index `k` and reduces to the first case.

The third index is needed. `St₂(R)` is the free product of two copies of `(R, +)`
(`TauCeti.IndexedSteinbergGroup.finTwoEquivCoprod`), so in `St₂(R × S)` the elements
`x_{01}(a, 0)` and `x_{10}(0, b)` do not commute when `a` and `b` are nonzero, while their images
in `St₂(R) × St₂(S)` do.

Restricting to the kernels of `St(R) →* GL_∞(R)` gives the product formula for Milnor's `K₂`:
`K₂(R × S) ≃* K₂(R) × K₂(S)`, with components the maps induced by the two projections. The
kernel is preserved because the projections are jointly injective on `GL_∞(R × S)`
(`TauCeti.StableGeneralLinearGroup.ker_map_fst_inf_ker_map_snd`).

## Main definitions

* `TauCeti.IndexedSteinbergGroup.inl`, `TauCeti.IndexedSteinbergGroup.inr`: the homomorphisms
  `St_ι(R) →* St_ι(R × S)` and `St_ι(S) →* St_ι(R × S)` on the two factors.
* `TauCeti.IndexedSteinbergGroup.prodEquiv`: `St_ι(R × S) ≃* St_ι(R) × St_ι(S)`, for index types
  in which every pair of distinct indices has a third index distinct from both.
* `TauCeti.AlgebraicK2.prodEquiv`: `K₂(R × S) ≃* K₂(R) × K₂(S)`.

## Main results

* `TauCeti.IndexedSteinbergGroup.commute_inl_inr`: the images of the two factors commute.
* `TauCeti.IndexedSteinbergGroup.prodEquiv_apply`,
  `TauCeti.IndexedSteinbergGroup.prodEquiv_symm_apply`: the components of `prodEquiv` are the
  maps induced by the projections, and its inverse is `(y, z) ↦ inl y * inr z`.
* `TauCeti.AlgebraicK2.prodEquiv_apply`, `TauCeti.AlgebraicK2.coe_prodEquiv_symm_apply`: the same
  formulas for `K₂`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5.
-/

public section

noncomputable section

open scoped commutatorElement

namespace TauCeti

namespace IndexedSteinbergGroup

variable {ι R S : Type*} [Ring R] [Ring S]

/-! ### The two factors of a product ring -/

variable (ι R S) in
/-- The homomorphism `St_ι(R) →* St_ι(R × S)` sending `x_{ij}(a)` to `x_{ij}(a, 0)`. It is induced
by the multiplicative, but not unital, map `a ↦ (a, 0)`. -/
def inl : IndexedSteinbergGroup ι R →* IndexedSteinbergGroup ι (R × S) :=
  lift (fun _ _ hij a ↦ x hij (a, 0))
    (fun _ _ hij a b ↦ by rw [← x_add, Prod.mk_add_mk, add_zero])
    (fun _ _ _ _ hij hkl hjk hli _ _ ↦ commute_x hij hkl hjk hli _ _)
    (fun _ _ _ hij hjk hik a b ↦ by rw [commutatorElement_x hij hjk hik, Prod.mk_mul_mk, mul_zero])

variable (ι R S) in
/-- The homomorphism `St_ι(S) →* St_ι(R × S)` sending `x_{ij}(b)` to `x_{ij}(0, b)`. It is induced
by the multiplicative, but not unital, map `b ↦ (0, b)`. -/
def inr : IndexedSteinbergGroup ι S →* IndexedSteinbergGroup ι (R × S) :=
  lift (fun _ _ hij b ↦ x hij (0, b))
    (fun _ _ hij a b ↦ by rw [← x_add, Prod.mk_add_mk, add_zero])
    (fun _ _ _ _ hij hkl hjk hli _ _ ↦ commute_x hij hkl hjk hli _ _)
    (fun _ _ _ hij hjk hik a b ↦ by rw [commutatorElement_x hij hjk hik, Prod.mk_mul_mk, mul_zero])

/-- `inl` sends `x_{ij}(a)` to `x_{ij}(a, 0)`. -/
@[simp]
theorem inl_x {i j : ι} (hij : i ≠ j) (a : R) : inl ι R S (x hij a) = x hij (a, 0) :=
  lift_x ..

/-- `inr` sends `x_{ij}(b)` to `x_{ij}(0, b)`. -/
@[simp]
theorem inr_x {i j : ι} (hij : i ≠ j) (b : S) : inr ι R S (x hij b) = x hij (0, b) :=
  lift_x ..

/-- The first projection undoes `inl`, as homomorphisms. -/
theorem map_fst_comp_inl : (map (RingHom.fst R S)).comp (inl ι R S) = MonoidHom.id _ := by
  ext i j hij a
  simp

/-- The second projection kills `inl`, as homomorphisms. -/
theorem map_snd_comp_inl : (map (RingHom.snd R S)).comp (inl ι R S) = 1 := by
  ext i j hij a
  simp

/-- The first projection kills `inr`, as homomorphisms. -/
theorem map_fst_comp_inr : (map (RingHom.fst R S)).comp (inr ι R S) = 1 := by
  ext i j hij b
  simp

/-- The second projection undoes `inr`, as homomorphisms. -/
theorem map_snd_comp_inr : (map (RingHom.snd R S)).comp (inr ι R S) = MonoidHom.id _ := by
  ext i j hij b
  simp

/-- The first projection undoes `inl`. -/
@[simp]
theorem map_fst_inl (y : IndexedSteinbergGroup ι R) :
    map (RingHom.fst R S) (inl ι R S y) = y :=
  DFunLike.congr_fun map_fst_comp_inl y

/-- The second projection kills the image of `inl`. -/
@[simp]
theorem map_snd_inl (y : IndexedSteinbergGroup ι R) :
    map (RingHom.snd R S) (inl ι R S y) = 1 :=
  DFunLike.congr_fun map_snd_comp_inl y

/-- The first projection kills the image of `inr`. -/
@[simp]
theorem map_fst_inr (z : IndexedSteinbergGroup ι S) :
    map (RingHom.fst R S) (inr ι R S z) = 1 :=
  DFunLike.congr_fun map_fst_comp_inr z

/-- The second projection undoes `inr`. -/
@[simp]
theorem map_snd_inr (z : IndexedSteinbergGroup ι S) :
    map (RingHom.snd R S) (inr ι R S z) = z :=
  DFunLike.congr_fun map_snd_comp_inr z

/-! ### The images of the two factors commute -/

/-- Generators with coefficients in the two factors commute unless their index pairs are opposite:
the defining relations give this, because `(a, 0) * (0, b) = 0 = (0, b) * (a, 0)`. -/
private theorem commute_x_x_of_not_opposite {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (h : ¬(j = k ∧ l = i)) (a : R) (b : S) :
    Commute (x hij ((a, 0) : R × S)) (x hkl ((0, b) : R × S)) := by
  by_cases hjk : j = k
  · subst hjk
    have hil : i ≠ l := fun hil ↦ h ⟨rfl, hil.symm⟩
    rw [← commutatorElement_eq_one_iff_commute, commutatorElement_x hij hkl hil, Prod.mk_mul_mk,
      mul_zero, zero_mul, Prod.mk_zero_zero, x_zero]
  · by_cases hli : l = i
    · subst hli
      refine Commute.symm ?_
      rw [← commutatorElement_eq_one_iff_commute, commutatorElement_x hkl hij (Ne.symm hjk),
        Prod.mk_mul_mk, mul_zero, zero_mul, Prod.mk_zero_zero, x_zero]
    · exact commute_x hij hkl hjk hli _ _

/-- When every pair of distinct indices has a third index distinct from both, the generators
`x_{ij}(a, 0)` and `x_{kl}(0, b)` commute for all index pairs. -/
private theorem commute_x_x (h : ∀ i j : ι, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j) {i j k l : ι}
    (hij : i ≠ j) (hkl : k ≠ l) (a : R) (b : S) :
    Commute (x hij ((a, 0) : R × S)) (x hkl ((0, b) : R × S)) := by
  by_cases hop : j = k ∧ l = i
  · obtain ⟨hjk, hli⟩ := hop
    subst k l
    obtain ⟨m, hmi, hmj⟩ := h i j hij
    have hx : x hij ((a, 0) : R × S) = ⁅x hmi.symm ((a, 0) : R × S), x hmj ((1, 0) : R × S)⁆ := by
      rw [commutatorElement_x hmi.symm hmj hij]
      simp
    -- Both factors of the commutator commute with `x_{ji}(0, b)`, hence so does the commutator.
    have h₁ := commute_x_x_of_not_opposite hmi.symm hkl (fun h ↦ hmj h.1) a b
    have h₂ := commute_x_x_of_not_opposite hmj hkl (fun h ↦ hmi h.2.symm) (1 : R) b
    rw [hx, commutatorElement_def]
    exact ((h₁.mul_left h₂).mul_left h₁.inv_left).mul_left h₂.inv_left
  · exact commute_x_x_of_not_opposite hij hkl hop a b

/-- When every pair of distinct indices has a third index distinct from both, the images of
`inl` and `inr` commute elementwise. -/
theorem commute_inl_inr (h : ∀ i j : ι, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j)
    (y : IndexedSteinbergGroup ι R) (z : IndexedSteinbergGroup ι S) :
    Commute (inl ι R S y) (inr ι R S z) := by
  induction y using IndexedSteinbergGroup.induction_on with
  | one => simp
  | mul y₁ y₂ h₁ h₂ => simpa using h₁.mul_left h₂
  | x hij a =>
    induction z using IndexedSteinbergGroup.induction_on with
    | one => simp
    | mul z₁ z₂ h₁ h₂ => simpa using h₁.mul_right h₂
    | x hkl b => simpa using commute_x_x h hij hkl a b

/-! ### The Steinberg group of a product ring -/

/-- **The Steinberg group of a product ring** is the product of the Steinberg groups:
`St_ι(R × S) ≃* St_ι(R) × St_ι(S)`, with components induced by the two projections, whenever every
pair of distinct indices in `ι` has a third index distinct from both. In `St₂` this fails, since
`St₂(R)` is a free product. -/
def prodEquiv (h : ∀ i j : ι, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j) :
    IndexedSteinbergGroup ι (R × S) ≃* IndexedSteinbergGroup ι R × IndexedSteinbergGroup ι S :=
  MonoidHom.toMulEquiv ((map (RingHom.fst R S)).prod (map (RingHom.snd R S)))
    ((inl ι R S).noncommCoprod (inr ι R S) (commute_inl_inr h))
    (by
      ext i j hij a
      simp [← x_add])
    (MonoidHom.ext fun p ↦ by simp)

/-- The components of `prodEquiv` are the maps induced by the two projections. -/
@[simp]
theorem prodEquiv_apply (h : ∀ i j : ι, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j)
    (w : IndexedSteinbergGroup ι (R × S)) :
    prodEquiv h w = (map (RingHom.fst R S) w, map (RingHom.snd R S) w) :=
  (rfl)

/-- The inverse of `prodEquiv` sends `(y, z)` to `inl y * inr z`. -/
@[simp]
theorem prodEquiv_symm_apply (h : ∀ i j : ι, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j)
    (p : IndexedSteinbergGroup ι R × IndexedSteinbergGroup ι S) :
    (prodEquiv h).symm p = inl ι R S p.1 * inr ι R S p.2 :=
  (rfl)

end IndexedSteinbergGroup

/-! ### `K₂` of a product ring -/

namespace AlgebraicK2

variable (R S : Type*) [Ring R] [Ring S]

/-- In `ℕ` every pair of distinct indices has a third index distinct from both. -/
private theorem nat_exists_ne_ne (i j : ℕ) (_ : i ≠ j) : ∃ k, k ≠ i ∧ k ≠ j :=
  ⟨i + j + 1, by omega, by omega⟩

private theorem prod_map_fst_map_snd_injective :
    Function.Injective ((map (RingHom.fst R S)).prod (map (RingHom.snd R S))) := by
  intro w w' hw
  simp only [MonoidHom.prod_apply, Prod.mk.injEq, Subtype.ext_iff, coe_map_apply] at hw
  refine Subtype.ext ((IndexedSteinbergGroup.prodEquiv nat_exists_ne_ne).injective ?_)
  simpa using hw

private theorem prod_map_fst_map_snd_surjective :
    Function.Surjective ((map (RingHom.fst R S)).prod (map (RingHom.snd R S))) := by
  rintro ⟨y, z⟩
  set w := (IndexedSteinbergGroup.prodEquiv nat_exists_ne_ne).symm ((y : SteinbergGroup R),
    (z : SteinbergGroup S))
  have hw := (IndexedSteinbergGroup.prodEquiv nat_exists_ne_ne).apply_symm_apply
    ((y : SteinbergGroup R), (z : SteinbergGroup S))
  rw [IndexedSteinbergGroup.prodEquiv_apply, Prod.mk.injEq] at hw
  have hker : w ∈ (SteinbergGroup.toStableGL (R × S)).ker := by
    -- Both projections of `toStableGL w` are the images of the `K₂` elements `y` and `z`.
    refine MonoidHom.mem_ker.2 (StableGeneralLinearGroup.eq_one_of_map_fst_eq_one_of_map_snd_eq_one
      ?_ ?_)
    · rw [← SteinbergGroup.toStableGL_map, hw.1, toStableGL_coe]
    · rw [← SteinbergGroup.toStableGL_map, hw.2, toStableGL_coe]
  refine ⟨⟨w, hker⟩, ?_⟩
  simp only [MonoidHom.prod_apply, Prod.mk.injEq, Subtype.ext_iff, coe_map_apply]
  exact hw

/-- **`K₂` of a product ring** is the product of the `K₂` groups: `K₂(R × S) ≃* K₂(R) × K₂(S)`,
with components the maps induced by the two projections. -/
def prodEquiv : AlgebraicK2 (R × S) ≃* AlgebraicK2 R × AlgebraicK2 S :=
  MulEquiv.ofBijective ((map (RingHom.fst R S)).prod (map (RingHom.snd R S)))
    ⟨prod_map_fst_map_snd_injective R S, prod_map_fst_map_snd_surjective R S⟩

variable {R S}

/-- The components of `AlgebraicK2.prodEquiv` are the maps induced by the two projections. -/
@[simp]
theorem prodEquiv_apply (w : AlgebraicK2 (R × S)) :
    prodEquiv R S w = (map (RingHom.fst R S) w, map (RingHom.snd R S) w) :=
  (rfl)

/-- The inverse of `prodEquiv` sends `(y, z)` to `inl y * inr z` in the Steinberg group of
`R × S`. -/
@[simp]
theorem coe_prodEquiv_symm_apply (p : AlgebraicK2 R × AlgebraicK2 S) :
    ((prodEquiv R S).symm p : SteinbergGroup (R × S)) =
      IndexedSteinbergGroup.inl ℕ R S p.1 * IndexedSteinbergGroup.inr ℕ R S p.2 := by
  refine (IndexedSteinbergGroup.prodEquiv nat_exists_ne_ne).injective ?_
  have h := (prodEquiv R S).apply_symm_apply p
  rw [prodEquiv_apply, Prod.ext_iff] at h
  dsimp only at h
  rw [IndexedSteinbergGroup.prodEquiv_apply, ← coe_map_apply, ← coe_map_apply, h.1, h.2]
  simp

end AlgebraicK2

end TauCeti
