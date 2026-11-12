/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Graded
public import Mathlib.Basic.Sign.Basic
public import TauCeti.Algebra.DirectSum.Internal

/-!
# Sign subalgebras of a graded Lie algebra

An additive functional on the grading indices separates a graded Lie algebra into
positive, zero and negative Lie subalgebras. Their underlying modules form an
internal direct sum. Thus every element has unique sign components, even though
the three projections need not be Lie homomorphisms. This is the linear splitting
used when factoring nilpotent group elements by the signs of their degrees.

The construction uses Mathlib's `SignType.sign` and graded bracket, and collects
the homogeneous decomposition with `DirectSum.IsInternal.iSup_fiber`.
No positivity, nilpotency, dimension or freeness assumption is needed here.

## Main results

* `TauCeti.signSubalgebra`: the Lie subalgebra of the pieces whose degree has a given sign.
* `TauCeti.isInternal_signSubalgebra`: the three sign subalgebras form an internal direct sum.
* `TauCeti.signDecomposition`: the resulting linear splitting into sign components.
* `TauCeti.signSubalgebra_eq_top_of_sign_eq`: a functional of one sign on every nonzero piece has
  the whole Lie algebra as its sign subalgebra.

## Provenance

Adapted from `Mei/Algebra/Lie/Graded/Sign/{Basic,Chamber}.lean` (the latter gives
`signSubalgebra_eq_top_of_sign_eq`) in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

noncomputable section

open scoped DirectSum

namespace TauCeti

variable {ι R L A : Type*} [AddCommMonoid ι]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommMonoid A] [LinearOrder A] [IsOrderedAddMonoid A]
  (ℒ : ι → Submodule R L) [SetLike.GradedBracket ℒ ℒ] (θ : ι →+ A)

/-- The sum of homogeneous pieces whose degree has sign `s` under `θ`.
The positive, zero and negative sums are each closed under the Lie bracket. -/
def signSubalgebra (s : SignType) : LieSubalgebra R L where
  toSubmodule := ⨆ n : {n // SignType.sign (θ n) = s}, ℒ n
  lie_mem' {x y} hx hy := by
    let S := ⨆ n : {n // SignType.sign (θ n) = s}, ℒ n
    refine Submodule.iSup_induction _ (motive := fun x => ⁅x, y⁆ ∈ S) hx
      (fun n x hx => ?_) (by simp [S])
      (fun x z hx hz => by simpa only [add_lie] using S.add_mem hx hz)
    refine Submodule.iSup_induction _ (motive := fun y => ⁅x, y⁆ ∈ S) hy
      (fun m y hy => ?_) (by simp [S])
      (fun y z hy hz => by simpa only [lie_add] using S.add_mem hy hz)
    have hnm : SignType.sign (θ (n.val + m.val)) = s := by
      rw [map_add]
      have hn := n.property
      have hm := m.property
      cases s with
      | zero => simp_all
      | neg =>
        simp only [SignType.neg_eq_neg_one, sign_eq_neg_one_iff] at hn hm ⊢
        exact Left.add_neg_of_neg_of_nonpos hn hm.le
      | pos =>
        simp only [SignType.pos_eq_one, sign_eq_one_iff] at hn hm ⊢
        exact Left.add_pos_of_pos_of_nonneg hn hm.le
    exact Submodule.mem_iSup_of_mem ⟨n.val + m.val, hnm⟩
      (SetLike.GradedBracket.bracket_mem hx hy)

omit [IsOrderedAddMonoid A] [SetLike.GradedBracket ℒ ℒ] in
/-- The underlying module is the sum over the specified sign fiber. -/
@[simp]
theorem signSubalgebra_toSubmodule [IsOrderedAddMonoid A] [SetLike.GradedBracket ℒ ℒ]
    (s : SignType) :
    (signSubalgebra ℒ θ s).toSubmodule =
      ⨆ n : {n // SignType.sign (θ n) = s}, ℒ n := (rfl)

/-- Every homogeneous piece belongs to the subalgebra of its sign. -/
theorem le_signSubalgebra (n : ι) :
    ℒ n ≤ (signSubalgebra ℒ θ (SignType.sign (θ n))).toSubmodule := by
  rw [signSubalgebra_toSubmodule]
  exact le_iSup (fun m : {m // SignType.sign (θ m) = SignType.sign (θ n)} => ℒ m) ⟨n, rfl⟩

/-- Taking images commutes with collecting homogeneous pieces by sign. -/
theorem map_signSubalgebra {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (ℳ : ι → Submodule R L') [SetLike.GradedBracket ℳ ℳ]
    (f : L →ₗ⁅R⁆ L') (hf : ∀ n, (ℒ n).map f.toLinearMap = ℳ n) (s : SignType) :
    (signSubalgebra ℒ θ s).map f = signSubalgebra ℳ θ s := by
  apply LieSubalgebra.toSubmodule_injective
  simp only [LieSubalgebra.map, signSubalgebra_toSubmodule, Submodule.map_iSup, hf]

/-- An implication between sign fibers on nonzero homogeneous pieces induces
an inclusion of the corresponding sign subalgebras. -/
theorem signSubalgebra_le_of_sign_imp (φ : ι →+ A) (s t : SignType)
    (h : ∀ n, ℒ n ≠ ⊥ → SignType.sign (θ n) = s → SignType.sign (φ n) = t) :
    signSubalgebra ℒ θ s ≤ signSubalgebra ℒ φ t := by
  rw [← LieSubalgebra.toSubmodule_le_toSubmodule, signSubalgebra_toSubmodule,
    signSubalgebra_toSubmodule]
  refine iSup_le fun n => ?_
  by_cases hn : ℒ n = ⊥
  · simp [hn]
  · exact le_iSup_of_le ⟨n, h n hn n.property⟩ le_rfl

/-- Sign subalgebras depend only on the signs of degrees with nonzero pieces. -/
theorem signSubalgebra_eq_of_sign_eq (φ : ι →+ A)
    (h : ∀ n, ℒ n ≠ ⊥ → SignType.sign (θ n) = SignType.sign (φ n))
    (s : SignType) : signSubalgebra ℒ θ s = signSubalgebra ℒ φ s :=
  le_antisymm
    (signSubalgebra_le_of_sign_imp ℒ θ φ s s fun n hn h' => (h n hn).symm.trans h')
    (signSubalgebra_le_of_sign_imp ℒ φ θ s s fun n hn h' => (h n hn).trans h')

variable {L' : Type*} [LieRing L'] [LieAlgebra R L']
  (ℳ : ι → Submodule R L') [SetLike.GradedBracket ℳ ℳ]

/-- An additive homomorphism preserving homogeneous degrees preserves each sign subalgebra. -/
theorem map_mem_signSubalgebra (f : L →+ L')
    (hf : ∀ n, ∀ x ∈ ℒ n, f x ∈ ℳ n) {s : SignType} {x : L}
    (hx : x ∈ signSubalgebra ℒ θ s) : f x ∈ signSubalgebra ℳ θ s := by
  rw [← LieSubalgebra.mem_toSubmodule, signSubalgebra_toSubmodule] at hx ⊢
  refine Submodule.iSup_induction _ (motive := fun x =>
    f x ∈ ⨆ n : {n // SignType.sign (θ n) = s}, ℳ n) hx
    (fun n x hx => Submodule.mem_iSup_of_mem n (hf n x hx))
    (by simp) (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)

variable [DecidableEq ι] [DirectSum.Decomposition ℒ]

/-- Membership is characterized by vanishing of the components of other signs. -/
theorem mem_signSubalgebra_iff {s : SignType} {x : L} :
    x ∈ signSubalgebra ℒ θ s ↔
      ∀ n, SignType.sign (θ n) ≠ s → (DirectSum.decompose ℒ x n : L) = 0 := by
  constructor
  · intro hx n hn
    rw [← LieSubalgebra.mem_toSubmodule, signSubalgebra_toSubmodule] at hx
    refine Submodule.iSup_induction _
      (motive := fun x => (DirectSum.decompose ℒ x n : L) = 0) hx
      (fun m x hx => ?_) (by simp) (fun x y hx hy => by simp [hx, hy])
    exact DirectSum.decompose_of_mem_ne ℒ hx (fun h => hn (h ▸ m.property))
  · intro hx
    classical
    rw [← DirectSum.sum_support_decompose ℒ x, ← LieSubalgebra.mem_toSubmodule,
      signSubalgebra_toSubmodule]
    apply Submodule.sum_mem
    intro n _
    by_cases hs : SignType.sign (θ n) = s
    · exact Submodule.mem_iSup_of_mem ⟨n, hs⟩ (DirectSum.decompose ℒ x n).property
    · rw [hx n hs]
      exact Submodule.zero_mem _

/-- Sign subalgebras are stable under every homogeneous projection. -/
theorem isHomogeneous_signSubalgebra (s : SignType) :
    DirectSum.SetLike.IsHomogeneous ℒ (signSubalgebra ℒ θ s) := by
  intro n x hx
  by_cases hs : SignType.sign (θ n) = s
  · rw [← hs]
    exact le_signSubalgebra ℒ θ n (DirectSum.decompose ℒ x n).property
  · rw [(mem_signSubalgebra_iff ℒ θ).mp hx n hs]
    exact (signSubalgebra ℒ θ s).zero_mem

/-- Collecting homogeneous pieces by sign gives an internal module decomposition. -/
theorem isInternal_signSubalgebra :
    DirectSum.IsInternal (fun s => (signSubalgebra ℒ θ s).toSubmodule) := by
  simp only [signSubalgebra_toSubmodule, iSup_subtype]
  exact (DirectSum.Decomposition.isInternal ℒ).iSup_fiber (fun n => SignType.sign (θ n))

/-- The sign subalgebras form a decomposition of the Lie algebra as a module. -/
instance : DirectSum.Decomposition (fun s => (signSubalgebra ℒ θ s).toSubmodule) :=
  (isInternal_signSubalgebra ℒ θ).chooseDecomposition

/-- The canonical linear decomposition into the three sign subalgebras.
It is a module equivalence, with inverse given by addition, rather than a Lie
equivalence to a product Lie algebra. -/
def signDecomposition : L ≃ₗ[R] ⨁ s, (signSubalgebra ℒ θ s).toSubmodule :=
  DirectSum.decomposeLinearEquiv _

open scoped Classical in
/-- A sign component is the finite sum of the homogeneous components of that sign. -/
theorem signDecomposition_apply (x : L) (s : SignType) :
    (signDecomposition ℒ θ x s : L) =
      ∑ n ∈ (DirectSum.decompose ℒ x).support,
        if SignType.sign (θ n) = s then (DirectSum.decompose ℒ x n : L) else 0 := by
  simpa [Finset.sum_filter, signDecomposition, DirectSum.decomposeLinearEquiv_apply] using
    DirectSum.decompose_map_eq_sum ℒ (fun s => (signSubalgebra ℒ θ s).toSubmodule)
      (AddMonoidHom.id L) (fun n => SignType.sign (θ n))
      (fun n _ hx => le_signSubalgebra ℒ θ n hx) x s

/-- Sign projections preserve homogeneous submodules. In particular, they preserve
the homogeneous ideals used in graded nilpotent truncations. -/
theorem signDecomposition_mem (K : Submodule R L)
    (hK : DirectSum.SetLike.IsHomogeneous ℒ K) {x : L} (hx : x ∈ K) (s : SignType) :
    (signDecomposition ℒ θ x s : L) ∈ K := by
  classical
  rw [signDecomposition_apply]
  apply K.sum_mem
  intro n _
  split
  · exact hK n hx
  · exact K.zero_mem

/-- Adding the three sign components recovers the original element. -/
theorem sum_signDecomposition (x : L) :
    ∑ s : SignType, (signDecomposition ℒ θ x s : L) = x := by
  have h := DirectSum.Decomposition.left_inv (M := L)
    (ℳ := fun s => (signSubalgebra ℒ θ s).toSubmodule) x
  rw [← DirectSum.sum_univ_of (DirectSum.Decomposition.decompose' x)] at h
  simpa [signDecomposition, DirectSum.decomposeLinearEquiv_apply] using h

/-- A functional with one sign on every nonzero piece has the whole Lie algebra as its subalgebra
of that sign. -/
theorem signSubalgebra_eq_top_of_sign_eq (s : SignType)
    (hs : ∀ n, ℒ n ≠ ⊥ → SignType.sign (θ n) = s) : signSubalgebra ℒ θ s = ⊤ := by
  apply LieSubalgebra.toSubmodule_injective
  apply top_unique
  rw [← (DirectSum.Decomposition.isInternal ℒ).submodule_iSup_eq_top]
  refine iSup_le fun n => ?_
  by_cases hn : ℒ n = ⊥
  · rw [hn]
    exact bot_le
  · rw [← hs n hn]
    exact le_signSubalgebra _ _ _

variable [DirectSum.Decomposition ℳ]

/-- Sign decomposition commutes with an additive homomorphism preserving homogeneous degrees. -/
theorem map_signDecomposition (f : L →+ L')
    (hf : ∀ n, ∀ x ∈ ℒ n, f x ∈ ℳ n) (x : L) (s : SignType) :
    f (signDecomposition ℒ θ x s : L) =
      (signDecomposition ℳ θ (f x) s : L') := by
  simpa [signDecomposition, DirectSum.decomposeLinearEquiv_apply] using
    DirectSum.map_decompose_shift (fun s => (signSubalgebra ℒ θ s).toSubmodule)
      (fun s => (signSubalgebra ℳ θ s).toSubmodule) f id Function.injective_id
      (fun _ _ hx => map_mem_signSubalgebra ℒ θ ℳ f hf hx) s x

end TauCeti
