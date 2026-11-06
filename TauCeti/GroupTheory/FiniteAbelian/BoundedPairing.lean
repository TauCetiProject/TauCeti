/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Hom
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval

/-!
# Elements of a finitely generated abelian group with bounded real pairings

Let `H` be a finitely generated abelian group and `θ i : H →+ ℝ` a family of real-valued
homomorphisms spanning the real vector space `H →+ ℝ`. Then only finitely many `A : H` have all
pairings `θ i A` in a bounded window: `{A | ∀ i, |θ i A| ≤ C i}` is finite
(`TauCeti.finite_setOf_forall_abs_apply_le`). Torsion elements are not lost: each window contains
whole cosets of the finite torsion subgroup.

The spanning hypothesis cannot be weakened to joint injectivity modulo torsion: for
`H = ℤ²` the single homomorphism `(a, b) ↦ a + b √2` vanishes only at zero, yet takes infinitely
many values in `[-1, 1]`.

The intended application is to pseudoholomorphic curves. There `H` is the integral homology
`H₂(X; ℤ)` of a closed manifold and the `θ i` are the pairings with a basis of closed two-forms,
which span `H²(X; ℝ) = Hom(H₂(X; ℤ), ℝ)` by de Rham's theorem. The classes `A` with `σ A ≤ a`
and `|θ i A| ≤ K i σ A` form a finite set
(`TauCeti.finite_setOf_apply_le_and_forall_abs_apply_le_mul`). The integral `∫_C u^* θ` over a
curve is bounded by the comass of `θ` times the symplectic area of the curve
(`TauCeti.abs_integralTopForm_mpullback_le`). Concluding that below an area cutoff only finitely
many homology classes carry pseudoholomorphic curves also requires identifying `∫_C u^* θ` with
the pairing of `[θ]` with the class of the curve. That de Rham comparison is not provided here.

## Implementation notes

By the structure theorem `H ≃+ ℤⁿ × T` with `T` finite
(`AddCommGroup.equiv_free_prod_directSum_zmod`). Each coordinate `ℤⁿ → ℤ` of the free part,
viewed as a real-valued homomorphism, is a finite real combination of the `θ i`, so it is bounded
on a window, whose free coordinates therefore range over a finite box.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347, §1.
-/
public section

open Set

namespace TauCeti

variable {H ι : Type*} [AddCommGroup H] [AddGroup.FG H]

/-- **Bounded real pairings cut out a finite set.** In a finitely generated abelian group `H`, if
the real-valued homomorphisms `θ i` span `H →+ ℝ`, then only finitely many elements have all
pairings `|θ i A| ≤ C i`. -/
theorem finite_setOf_forall_abs_apply_le (θ : ι → H →+ ℝ)
    (hθ : Submodule.span ℝ (range θ) = ⊤) (C : ι → ℝ) :
    {A : H | ∀ i, |θ i A| ≤ C i}.Finite := by
  classical
  obtain ⟨n, κ, _, p, hp, e, ⟨φ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod H
  -- The torsion part of the structure theorem is finite.
  have : ∀ i, NeZero (p i ^ e i) := fun i ↦ ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : Finite (DirectSum κ fun i ↦ ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  -- The coordinates of the free part, as real-valued homomorphisms.
  let g (j : Fin n) : H →+ ℝ :=
    (Int.castAddHom ℝ).comp ((Finsupp.applyAddHom j).comp
      ((AddMonoidHom.fst _ _).comp φ.toAddMonoidHom))
  have hg (j : Fin n) (A : H) : g j A = ((φ A).1 j : ℝ) := rfl
  -- Each coordinate is a finite combination of the `θ i`, hence bounded on the window.
  have hbound (j : Fin n) : ∃ K : ℕ, ∀ A : H, (∀ i, |θ i A| ≤ C i) → |(φ A).1 j| ≤ K := by
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
      (hθ ▸ Submodule.mem_top : g j ∈ Submodule.span ℝ (range θ))
    refine ⟨⌈∑ i ∈ c.support, |c i| * C i⌉₊, fun A hA ↦ ?_⟩
    have hA' : |((φ A).1 j : ℝ)| ≤ ∑ i ∈ c.support, |c i| * C i := by
      have hsum : g j A = ∑ i ∈ c.support, c i * θ i A := by
        rw [← hc]
        simp [Finsupp.sum]
      rw [← hg, hsum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hA i) (abs_nonneg _)
    exact_mod_cast hA'.trans (Nat.le_ceil _)
  choose K hK using hbound
  -- The window maps injectively into a finite box times the torsion part.
  let box : Set ((Fin n → ℤ) × DirectSum κ fun i ↦ ZMod (p i ^ e i)) :=
    (univ.pi fun j ↦ Icc (-(K j : ℤ)) (K j)) ×ˢ univ
  have hbox : box.Finite := (Finite.pi fun j ↦ finite_Icc _ _).prod finite_univ
  let ψ : H → (Fin n → ℤ) × DirectSum κ fun i ↦ ZMod (p i ^ e i) :=
    fun A ↦ (⇑(φ A).1, (φ A).2)
  have hψ : ψ.Injective := by
    intro A B h
    apply φ.injective
    simp only [ψ, Prod.mk.injEq] at h
    exact Prod.ext (DFunLike.coe_injective h.1) h.2
  refine (hbox.preimage hψ.injOn).subset fun A hA ↦ ?_
  simp only [box, ψ, mem_preimage, mem_prod, mem_pi, mem_univ, forall_const, and_true]
  exact fun j ↦ abs_le.1 (hK j A hA)

/-- **Finitely many classes below an area cutoff.** In a finitely generated abelian group `H`,
let the real-valued homomorphisms `θ i` span `H →+ ℝ`, and let `σ : H →+ ℝ` and `K i ≥ 0`. Then
only finitely many `A` satisfy `σ A ≤ a` and `|θ i A| ≤ K i * σ A` for all `i`. These are the
bounds expected from the area `σ A` of a pseudoholomorphic curve in the class `A` on its pairings
with closed two-forms of comass at most `K i`, once integrals over curves are identified with
pairings of homology classes. -/
theorem finite_setOf_apply_le_and_forall_abs_apply_le_mul (θ : ι → H →+ ℝ)
    (hθ : Submodule.span ℝ (range θ) = ⊤) (σ : H →+ ℝ) {K : ι → ℝ} (hK : ∀ i, 0 ≤ K i)
    (a : ℝ) : {A : H | σ A ≤ a ∧ ∀ i, |θ i A| ≤ K i * σ A}.Finite :=
  (finite_setOf_forall_abs_apply_le θ hθ fun i ↦ K i * a).subset fun _ hA i ↦
    (hA.2 i).trans (mul_le_mul_of_nonneg_left hA.1 (hK i))

end TauCeti
