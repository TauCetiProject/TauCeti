/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.RingTheory.Invariant.EquivalenceRelation.Basic

/-!
# Equivalence relations with a basis coming from the base

Let `s = algebraMap A B` and `t : A →+* B` define an equivalence relation `Spec B ⇉ Spec A`
(`RingHom.IsSpecEquivRel`), with ring of invariants `C = {a : s a = t a}`. Suppose that there are
elements `aᵢ ∈ A` whose images `t aᵢ` form a basis of `B` as an `A`-module through `s`. This file
proves that then

* the `aᵢ` form a basis of `A` as a `C`-module (`RingHom.IsSpecEquivRel.basis`), and the
  coordinates of `x ∈ A` in it are the coordinates of `t x` in the given basis of `B`;
* the map `A ⊗[C] A → B`, `x ⊗ y ↦ s x * t y`, is an isomorphism of `A`-algebras
  (`RingHom.IsSpecEquivRel.tensorProductEquiv`).

Geometrically, `Spec A ⟶ Spec C` is then finite free (when the index set is finite), and the
relation is its kernel pair: `Spec B ≅ Spec A ×_{Spec C} Spec A`. This is the local step of the
construction of the quotient of an affine scheme by a finite locally free equivalence relation
(SGA 3, Exposé V, Théorème 4.1): when `C` is local, such elements `aᵢ` exist, and the quotient is
`Spec C`.

The coordinates of `t x` are invariants by the following argument. Write `t x = ∑ s(cᵢ) t(aᵢ)`.
On `B ⊗[A] B`, whose points are pairs of related pairs `((u, v), (u, w))`, there are two ring
homomorphisms from `B`: the inclusion of the second factor, `(u, w)`, and the composite
`(v, w) = (u, w) ∘ (u, v)⁻¹`, given by transitivity and the inversion of the relation. Applying
both to the expansion of `t x` gives two expansions of `1 ⊗ t x` in the basis `1 ⊗ t aᵢ` of
`B ⊗[A] B` over its first factor, with coefficients `s cᵢ ⊗ 1` and `t cᵢ ⊗ 1`. Comparing them
gives `s cᵢ = t cᵢ`.

## Main definitions

* `RingHom.IsSpecEquivRel.basis`: the basis of `A` over the ring of invariants.
* `RingHom.IsSpecEquivRel.tensorProductEquiv`: the isomorphism `A ⊗[C] A ≃ₐ[A] B`.

## Main results

* `RingHom.IsSpecEquivRel.repr_mem_eqLocus`: the coordinates of `t x` are invariants.
* `RingHom.IsSpecEquivRel.coe_basis_repr_apply`: the coordinates in `basis` are those of `t x`.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §4.
* The Stacks Project, Chapter *Groupoid Schemes*, Section *Finite flat groupoids, affine case*.
-/

public section

universe u

open TensorProduct Algebra.TensorProduct

namespace RingHom.IsSpecEquivRel

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {t : A →+* B}
  (h : (algebraMap A B).IsSpecEquivRel t) {ι : Type*} (b : Module.Basis ι A B) {a : ι → A}
  (hb : ∀ i, b i = t (a i))

-- a ring homomorphism out of `B` applied to the expansion of `y` in the basis `b`
private theorem map_eq_sum_repr {T : Type*} [CommRing T] (φ : B →+* T) (y : B) :
    φ y = (b.repr y).sum fun i r ↦ φ (algebraMap A B r) * φ (b i) := by
  conv_lhs => rw [← b.linearCombination_repr y]
  simp [Finsupp.linearCombination_apply, map_finsuppSum, Algebra.smul_def]

-- in `B ⊗[A] B`, a sum of `(u r ⊗ 1) * (1 ⊗ b i)` is a linear combination of the base-changed
-- basis over the first factor
private theorem sum_eq_linearCombination (u : A →+* B) (c : ι →₀ A) :
    (c.sum fun i r ↦ (u r ⊗ₜ[A] (1 : B)) * (1 ⊗ₜ b i)) =
      Finsupp.linearCombination B (Algebra.TensorProduct.basis B b)
        (c.mapRange u (map_zero u)) := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
  simp [Algebra.smul_def]

include hb

-- `t` carries a linear combination of the `aᵢ` with invariant coefficients to the same linear
-- combination of the basis vectors `t aᵢ`
private theorem map_linearCombination (r : ι →₀ (algebraMap A B).eqLocus t) :
    t (Finsupp.linearCombination _ a r) =
      Finsupp.linearCombination A b (r.mapRange Subtype.val rfl) := by
  have ht (c : (algebraMap A B).eqLocus t) : t (algebraMap _ A c) = algebraMap A B c :=
    (mem_eqLocus.mp c.2).symm
  simp [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index, map_finsuppSum,
    Algebra.smul_def, hb, ht]

private theorem linearIndependent : LinearIndependent ((algebraMap A B).eqLocus t) a := by
  refine linearIndependent_iff.mpr fun r hr ↦ ?_
  have := map_linearCombination b hb r
  rw [hr, map_zero] at this
  exact Finsupp.mapRange_injective _ rfl Subtype.val_injective
    (by simpa using linearIndependent_iff.mp b.linearIndependent _ this.symm)

include h

/-- **The coordinates of `t x` are invariants.** If the images `t aᵢ` of elements of `A` form a
basis of `B` over `A`, then the coordinates of every `t x` in this basis lie in the ring of
invariants `{a : s a = t a}`. -/
theorem repr_mem_eqLocus (x : A) (i : ι) :
    b.repr (t x) i ∈ (algebraMap A B).eqLocus t := by
  -- the composite `(v, w) = (u, w) ∘ (u, v)⁻¹` on points `((u, v), (u, w))` of `B ⊗[A] B`
  obtain ⟨z, hzs, hzt⟩ := h.exists_comp_algebraMap_eq_includeLeft_and_comp_eq_includeRight
  have hzs' (r : A) : z (algebraMap A B r) = t r ⊗ₜ 1 := by
    simpa using congr($hzs r)
  have hzt' (r : A) : z (t r) = 1 ⊗ₜ t r := congr($hzt r)
  -- expanding `1 ⊗ t x` through `z` and through the second inclusion gives two coordinate
  -- vectors in the basis `1 ⊗ t aᵢ` of `B ⊗[A] B` over its first factor
  have h₁ := map_eq_sum_repr b z (t x)
  have h₂ := map_eq_sum_repr b (includeRight.toRingHom : B →+* B ⊗[A] B) (t x)
  simp only [hzs', hzt', hb] at h₁
  simp only [AlgHom.toRingHom_eq_coe, coe_coe, includeRight_apply, hb,
    ← tmul_one_eq_one_tmul] at h₂
  simp only [← hb, sum_eq_linearCombination] at h₁ h₂
  have := congr((Algebra.TensorProduct.basis B b).repr $(h₂.symm.trans h₁) i)
  simpa using this

-- the expansion of `x` in the `aᵢ`, with the coordinates of `t x`
private theorem sum_repr_mul (x : A) : ((b.repr (t x)).sum fun i r ↦ r * a i) = x := by
  -- evaluate the expansion of `t x` at the diagonal point of `Spec B`
  obtain ⟨e, hes, het⟩ := h.refl (RingHom.id A)
  have hes' (r : A) : e (algebraMap A B r) = r := congr($hes r)
  have het' (r : A) : e (t r) = r := congr($het r)
  simpa [hes', het', hb] using (map_eq_sum_repr b e (t x)).symm

private theorem top_le_span :
    ⊤ ≤ Submodule.span ((algebraMap A B).eqLocus t) (Set.range a) := by
  intro x _
  rw [← sum_repr_mul h b hb x]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  exact Submodule.smul_mem _ (⟨_, h.repr_mem_eqLocus b hb x i⟩ : (algebraMap A B).eqLocus t)
    (Submodule.subset_span ⟨i, rfl⟩)

/-- **A basis of `A` over the invariants.** If the images `t aᵢ` of elements `aᵢ` of `A` form a
basis of `B` over `A`, then the `aᵢ` form a basis of `A` over the ring of invariants
`{a : s a = t a}`. -/
noncomputable def basis : Module.Basis ι ((algebraMap A B).eqLocus t) A :=
  .mk (linearIndependent b hb) (top_le_span h b hb)

/-- The vectors of `RingHom.IsSpecEquivRel.basis` are the given elements `aᵢ`. -/
@[simp]
theorem coe_basis : ⇑(h.basis b hb) = a :=
  Module.Basis.coe_mk _ _

/-- The coordinates of `x` in `RingHom.IsSpecEquivRel.basis` are the coordinates of `t x` in the
given basis of `B`. -/
@[simp]
theorem coe_basis_repr_apply (x : A) (i : ι) : ((h.basis b hb).repr x i : A) = b.repr (t x) i := by
  have hx : Finsupp.linearCombination _ a ((h.basis b hb).repr x) = x := by
    simpa using (h.basis b hb).linearCombination_repr x
  have := congr(b.repr $(map_linearCombination b hb ((h.basis b hb).repr x)) i)
  rw [hx] at this
  simpa using this.symm

/-- **The relation is the kernel pair of the quotient.** If the images `t aᵢ` of elements of `A`
form a basis of `B` over `A`, then `x ⊗ y ↦ s x * t y` is an isomorphism of `A`-algebras
`A ⊗[C] A ≃ₐ[A] B`, where `C = {a : s a = t a}` is the ring of invariants. -/
noncomputable def tensorProductEquiv : A ⊗[(algebraMap A B).eqLocus t] A ≃ₐ[A] B :=
  let f := Algebra.TensorProduct.lift (Algebra.ofId A B)
    (AlgHom.mk t fun c ↦ by
      simpa [IsScalarTower.algebraMap_apply _ A B, Algebra.algebraMap_ofSubsemiring_apply] using
        (mem_eqLocus.mp c.2).symm) fun _ _ ↦ .all _ _
  .ofBijective f <| by
    -- `f` carries the basis `1 ⊗ aᵢ` of `A ⊗[C] A` over `A` to the basis `t aᵢ` of `B`
    let bA := Algebra.TensorProduct.basis A (h.basis b hb)
    have hf : f.toLinearMap = (bA.equiv b (Equiv.refl ι)).toLinearMap :=
      bA.ext fun i ↦ by
        rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
        simp [bA, f, hb]
    rw [← AlgHom.coe_toLinearMap, hf]
    exact (bA.equiv b (Equiv.refl ι)).bijective

/-- The isomorphism `A ⊗[C] A ≃ₐ[A] B` sends `x ⊗ y` to `s x * t y`. -/
@[simp]
theorem tensorProductEquiv_tmul (x y : A) :
    h.tensorProductEquiv b hb (x ⊗ₜ y) = algebraMap A B x * t y := by
  simp [tensorProductEquiv]

end RingHom.IsSpecEquivRel
