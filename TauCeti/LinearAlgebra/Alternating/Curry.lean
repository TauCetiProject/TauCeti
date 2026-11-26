/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Currying and uncurrying alternating maps

Mathlib's `AlternatingMap.curryLeft` turns an alternating map `f` in `n + 2` arguments into a
linear family `x ↦ f.curryLeft x` of alternating maps in `n + 1` arguments, and every member of
that family vanishes once its first argument is `x` again (`AlternatingMap.curryLeft_same`). This
file constructs the inverse: a linear family `g` of alternating maps with `(g x).curryLeft x = 0`
for every `x` assembles into the alternating map `AlternatingMap.uncurryLeft g hg` with
`uncurryLeft g hg v = g (v 0) (Fin.tail v)`.

So an alternating map may be defined by giving its value with the first argument fixed, and
checking only that it vanishes when the first two arguments agree. This is how the
Chevalley–Eilenberg differential, defined degree by degree through its interior products, is
shown to be alternating. The file also records that alternating maps are determined by their
interior products (`AlternatingMap.curryLeft_injective`) and that interior products anticommute
(`AlternatingMap.curryLeft_curryLeft_eq_neg`). If `ι_x f = 0`, then `f` vanishes on every family
with `x` in some slot (`AlternatingMap.map_eq_zero_of_curryLeft_eq_zero`) and does not see the
components of its arguments along `x` (`AlternatingMap.map_add_smul_of_curryLeft_eq_zero`): this
is how a form whose contraction with a vector field vanishes descends along that field.

Fixing the arguments of an alternating map `f` on `ι ⊕ κ` indexed by `ι` leaves an alternating map
of the arguments indexed by `κ`, and this depends alternatingly on the fixed arguments:
`AlternatingMap.currySum f` is the resulting alternating map with values in alternating maps, with
`f.currySum x v = f (Sum.elim x v)`. It is linear in `f` (`AlternatingMap.currySumLinearMap`) and
injective (`AlternatingMap.currySum_injective`).
-/

public section

open Fin

namespace AlternatingMap

variable {R M N : Type*} {n : ℕ}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- An alternating map in at least one argument is determined by its interior products. -/
theorem curryLeft_injective :
    Function.Injective (curryLeft : M [⋀^Fin (n + 1)]→ₗ[R] N → M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) := by
  intro f g h
  ext v
  have hv := congr(($h (v 0)) (tail v))
  rwa [curryLeft_apply_apply, curryLeft_apply_apply, Matrix.vecCons, cons_self_tail] at hv

/-- Interior products anticommute: exchanging the first two arguments changes the sign. -/
theorem curryLeft_curryLeft_eq_neg {N : Type*} [AddCommGroup N] [Module R N]
    (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (x y : M) :
    (f.curryLeft x).curryLeft y = -(f.curryLeft y).curryLeft x := by
  ext r
  simp only [curryLeft_apply_apply, neg_apply]
  rw [← f.map_swap (Matrix.vecCons y (Matrix.vecCons x r)) (zero_ne_one' (Fin (n + 2)))]
  rw [Matrix.cons_cons_comp_swap_zero_one]

/-- A linear family `g` of alternating maps in `n + 1` arguments, each vanishing when its first
argument equals the parameter, assembles into an alternating map in `n + 2` arguments whose first
argument is the parameter. This inverts `AlternatingMap.curryLeft`. -/
def uncurryLeft (g : M →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] N) (hg : ∀ x, (g x).curryLeft x = 0) :
    M [⋀^Fin (n + 2)]→ₗ[R] N where
  toMultilinearMap := (toMultilinearMapLM ∘ₗ g).uncurryLeft
  map_eq_zero_of_eq' v i j hv hij := by
    rw [MultilinearMap.toFun_eq_coe, LinearMap.uncurryLeft_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, toMultilinearMapLM_apply,
      coe_multilinearMap]
    -- Two equal arguments after the first make `g (v 0)` vanish; otherwise one of them is the
    -- first argument, and moving the other one next to it uses `hg`.
    wlog hle : i < j generalizing i j
    · exact this j i hv.symm hij.symm (lt_of_le_of_ne (not_lt.1 hle) hij.symm)
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hij.symm
      have hfront (w : Fin (n + 1) → M) (hw : w 0 = v 0) : g (v 0) w = 0 := by
        rw [← cons_self_tail w, hw, ← Matrix.vecCons, ← curryLeft_apply_apply, hg, zero_apply]
      rcases eq_or_ne j 0 with rfl | hj
      · exact hfront _ hv.symm
      · simpa [hfront (tail v ∘ Equiv.swap 0 j) (by simp [tail, hv])] using
          (g (v 0)).map_swap_add (tail v) hj.symm
    · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 (Fin.ne_zero_of_lt hle)
      exact (g (v 0)).map_eq_zero_of_eq (tail v) hv (ne_of_apply_ne succ hij)

/-- The first argument of `uncurryLeft g hg` selects the member of the family `g`. -/
@[simp]
theorem uncurryLeft_apply (g : M →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] N)
    (hg : ∀ x, (g x).curryLeft x = 0) (v : Fin (n + 2) → M) :
    uncurryLeft g hg v = g (v 0) (tail v) := (rfl)

/-- Currying `uncurryLeft g hg` recovers the family `g`. -/
@[simp]
theorem curryLeft_uncurryLeft (g : M →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] N)
    (hg : ∀ x, (g x).curryLeft x = 0) : (uncurryLeft g hg).curryLeft = g := by
  ext x v
  simp

/-- Uncurrying the interior products of `f` recovers `f`. -/
@[simp]
theorem uncurryLeft_curryLeft (f : M [⋀^Fin (n + 2)]→ₗ[R] N) :
    uncurryLeft f.curryLeft f.curryLeft_same = f := by
  ext v
  rw [uncurryLeft_apply, curryLeft_apply_apply]
  exact congrArg f (cons_self_tail v)

/-- If the interior product `ι_x f` vanishes, then `f` vanishes on every family of vectors with
`x` in some slot, not only in the first one. -/
theorem map_eq_zero_of_curryLeft_eq_zero {f : M [⋀^Fin (n + 1)]→ₗ[R] N} {x : M}
    (hx : f.curryLeft x = 0) {v : Fin (n + 1) → M} {j : Fin (n + 1)} (hv : v j = x) :
    f v = 0 := by
  -- Evaluating `ι_x f = 0` on the tail of `w` gives `f w = 0` when `x` is the first entry.
  have hfront (w : Fin (n + 1) → M) (hw : w 0 = x) : f w = 0 := by
    simpa [curryLeft_apply_apply, Matrix.vecCons, ← hw] using congr(($hx) (tail w))
  rcases eq_or_ne j 0 with rfl | hj
  · exact hfront v hv
  · have h := f.map_swap_add v hj.symm
    rwa [hfront (v ∘ Equiv.swap 0 j) (by simpa using hv), zero_add] at h

/-- If the interior product `ι_x f` vanishes, then `f` does not see the components of its
arguments along `x`: `f (v₀ + a₀ x, …, vₙ + aₙ x) = f (v₀, …, vₙ)`. -/
theorem map_add_smul_of_curryLeft_eq_zero {f : M [⋀^Fin (n + 1)]→ₗ[R] N} {x : M}
    (hx : f.curryLeft x = 0) (v : Fin (n + 1) → M) (a : Fin (n + 1) → R) :
    f (fun i ↦ v i + a i • x) = f v := by
  classical
  -- Every slot outside `s` holds a multiple of `x`, so if some slot lies outside `s` the term
  -- vanishes.
  have hterm (s : Finset (Fin (n + 1))) (hs : s ≠ Finset.univ) :
      f (s.piecewise v fun i ↦ a i • x) = 0 := by
    obtain ⟨j, hj⟩ := not_forall.1 (mt Finset.eq_univ_of_forall hs)
    have hupd : s.piecewise v (fun i ↦ a i • x) =
        Function.update (s.piecewise v fun i ↦ a i • x) j (a j • x) := by
      simp [hj]
    rw [hupd, f.map_update_smul,
      map_eq_zero_of_curryLeft_eq_zero hx (Function.update_self _ _ _), smul_zero]
  -- Expand `f (v + a • x)` over the subsets of the slots: only the term with `v` in every slot
  -- survives.
  calc f (fun i ↦ v i + a i • x) = ∑ s : Finset (Fin (n + 1)), f (s.piecewise v fun i ↦ a i • x) :=
        f.map_add_univ v fun i ↦ a i • x
    _ = f v := by
      rw [Finset.sum_eq_single Finset.univ (fun s _ hs ↦ hterm s hs) (by simp)]
      simp

section CurrySum

variable {ι κ : Type*}

/-- An alternating map on `ι ⊕ κ` as an alternating map of the arguments indexed by `ι`, with
values in alternating maps of the arguments indexed by `κ`. -/
def currySum (f : M [⋀^ι ⊕ κ]→ₗ[R] N) : M [⋀^ι]→ₗ[R] M [⋀^κ]→ₗ[R] N where
  toFun x :=
    { f.toMultilinearMap.currySum x with
      map_eq_zero_of_eq' v i j hv hij :=
        f.map_eq_zero_of_eq _ (i := .inr i) (j := .inr j) (by simpa using hv) (by simpa using hij) }
  map_update_add' x i a b := by
    ext v
    exact congr($(f.toMultilinearMap.currySum.map_update_add x i a b) v)
  map_update_smul' x i a b := by
    ext v
    exact congr($(f.toMultilinearMap.currySum.map_update_smul x i a b) v)
  map_eq_zero_of_eq' x i j hx hij := by
    ext v
    exact f.map_eq_zero_of_eq _ (i := .inl i) (j := .inl j) (by simpa using hx) (by simpa using hij)

/-- `f.currySum x v` evaluates `f` on the arguments `x` followed by the arguments `v`. -/
@[simp]
theorem currySum_apply (f : M [⋀^ι ⊕ κ]→ₗ[R] N) (x : ι → M) (v : κ → M) :
    f.currySum x v = f (Sum.elim x v) := (rfl)

/-- As a multilinear map, `f.currySum x` is the multilinear currying of `f` at `x`. -/
@[simp]
theorem currySum_apply_toMultilinearMap (f : M [⋀^ι ⊕ κ]→ₗ[R] N) (x : ι → M) :
    (f.currySum x).toMultilinearMap = f.toMultilinearMap.currySum x := (rfl)

/-- Currying the zero map along the sum gives zero. -/
@[simp]
theorem currySum_zero : currySum (0 : M [⋀^ι ⊕ κ]→ₗ[R] N) = 0 := by
  ext x v
  simp

/-- Currying along the sum is additive. -/
@[simp]
theorem currySum_add (f g : M [⋀^ι ⊕ κ]→ₗ[R] N) : (f + g).currySum = f.currySum + g.currySum := by
  ext x v
  simp

/-- Currying along the sum commutes with scalar multiplication. -/
@[simp]
theorem currySum_smul (r : R) (f : M [⋀^ι ⊕ κ]→ₗ[R] N) : (r • f).currySum = r • f.currySum := by
  ext x v
  simp

/-- `AlternatingMap.currySum` as a linear map. -/
def currySumLinearMap : (M [⋀^ι ⊕ κ]→ₗ[R] N) →ₗ[R] M [⋀^ι]→ₗ[R] M [⋀^κ]→ₗ[R] N where
  toFun f := f.currySum
  map_add' := currySum_add
  map_smul' := currySum_smul

/-- `AlternatingMap.currySumLinearMap` applies `AlternatingMap.currySum`. -/
@[simp]
theorem currySumLinearMap_apply (f : M [⋀^ι ⊕ κ]→ₗ[R] N) : currySumLinearMap f = f.currySum :=
  (rfl)

/-- An alternating map on `ι ⊕ κ` is determined by its currying along the sum. -/
theorem currySum_injective :
    Function.Injective (currySum : M [⋀^ι ⊕ κ]→ₗ[R] N → M [⋀^ι]→ₗ[R] M [⋀^κ]→ₗ[R] N) := by
  intro f g h
  ext w
  have hw := congr(($h (w ∘ Sum.inl)) (w ∘ Sum.inr))
  rwa [currySum_apply, currySum_apply, Sum.elim_comp_inl_inr] at hw

/-- Two alternating maps on `ι ⊕ κ` agree if and only if their curryings along the sum agree. -/
@[simp]
theorem currySum_inj {f g : M [⋀^ι ⊕ κ]→ₗ[R] N} : f.currySum = g.currySum ↔ f = g :=
  currySum_injective.eq_iff

/-- The currying of `f` along the sum vanishes if and only if `f` does. -/
@[simp]
theorem currySum_eq_zero {f : M [⋀^ι ⊕ κ]→ₗ[R] N} : f.currySum = 0 ↔ f = 0 := by
  rw [← currySum_zero, currySum_inj]

/-- Currying along the sum commutes with composing with a linear map on the values. -/
@[simp]
theorem currySum_compAlternatingMap {N₂ : Type*} [AddCommMonoid N₂] [Module R N₂]
    (g : N →ₗ[R] N₂) (f : M [⋀^ι ⊕ κ]→ₗ[R] N) (x : ι → M) :
    (g.compAlternatingMap f).currySum x = g.compAlternatingMap (f.currySum x) := by
  ext v
  simp

/-- Currying along the sum commutes with precomposing every argument with a linear map. -/
@[simp]
theorem currySum_compLinearMap {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂] (g : M₂ →ₗ[R] M)
    (f : M [⋀^ι ⊕ κ]→ₗ[R] N) (x : ι → M₂) :
    (f.compLinearMap g).currySum x = (f.currySum (g ∘ x)).compLinearMap g := by
  ext v
  simp only [currySum_apply, compLinearMap_apply]
  congr 1
  ext (i | k) <;> simp

end CurrySum

end CommSemiring

section AddCommGroup

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommGroup N] [Module R N]
  {ι κ : Type*}

/-- Currying along the sum commutes with negation. -/
@[simp]
theorem currySum_neg (f : M [⋀^ι ⊕ κ]→ₗ[R] N) : (-f).currySum = -f.currySum := by
  ext x v
  simp

/-- Currying along the sum commutes with subtraction. -/
@[simp]
theorem currySum_sub (f g : M [⋀^ι ⊕ κ]→ₗ[R] N) : (f - g).currySum = f.currySum - g.currySum := by
  ext x v
  simp

end AddCommGroup

end AlternatingMap
