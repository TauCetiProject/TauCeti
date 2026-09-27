/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension

/-!
# The norm of a finite subextension as a product over the absolute Galois group

Let `K` be a field, `Kˢ` a separable closure, `L/K` a finite extension and `σ : L →ₐ[K] Kˢ` a
`K`-embedding. Composing with `σ` identifies the coset space of the open subgroup
`Gal(Kˢ/σ(L))` cut out by `σ` with the set of `K`-embeddings of `L` into `Kˢ`,

```text
G_K ⧸ Gal(Kˢ/σ(L)) ≃ (L →ₐ[K] Kˢ),    g ↦ g ∘ σ,
```

and under that identification the classical formula "the norm is the product of the conjugates"
becomes a product over a system `t` of coset representatives:

```text
algebraMap K Kˢ (N_{L/K} b) = ∏ u : G_K ⧸ Gal(Kˢ/σ(L)), t u (σ b).
```

This is the shape in which the norm of a finite extension meets the cohomology of `G_K`, where a
sum `x ↦ ∑ u, t u • x` over a transversal is the standard degree-zero corestriction: on units of
`Kˢ` fixed by `Gal(Kˢ/σ(L))`, that sum is the norm of `L/K`.

Separability of `L/K` is not assumed. An embedding of `L` into a separable closure of `K` forces
it, because the minimal polynomial of `x : L` over `K` is that of `σ x`, and the argument is
recorded as `TauCeti.algebra_isSeparable_of_algHom_separableClosure`. Finiteness of `L/K` is used
twice: it bounds the index of `Gal(Kˢ/σ(L))` by `[L : K]`, so that the coset space is a finite
index set, and it is the hypothesis of Mathlib's product formula for the norm.

## Main definitions

* `TauCeti.fixingSubgroupQuotientEquivAlgHom`: the bijection between the cosets of
  `Gal(Kˢ/σ(L))` and the `K`-embeddings of `L` into `Kˢ`.

## Main results

* `TauCeti.algebra_isSeparable_of_algHom_separableClosure`: a field embedding over `K` into a
  separable closure of `K` is separable over `K`.
* `TauCeti.algebraMap_norm_eq_prod_transversal`: the norm of `L/K` is the product of the
  conjugates of `σ`, indexed by a transversal of `Gal(Kˢ/σ(L))`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I §5, where
  the degree-zero corestriction along a finite extension of fields is the norm.
-/

public section

noncomputable section

namespace TauCeti

open IntermediateField

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K)

include σ

/-- **A field with a `K`-embedding into a separable closure of `K` is separable over `K`**: the
minimal polynomial of `x` over `K` is the minimal polynomial of `σ x`, which is separable. -/
theorem algebra_isSeparable_of_algHom_separableClosure : Algebra.IsSeparable K L :=
  ⟨fun x => by
    simpa only [IsSeparable, minpoly.algHom_eq σ σ.injective] using
      Algebra.IsSeparable.isSeparable K (σ x)⟩

/-- Every `K`-embedding of `L` into `Kˢ` is `σ` moved by an automorphism of `Kˢ`: two embeddings
into a normal extension differ by an element of its automorphism group. -/
theorem exists_algHom_comp_eq (f : L →ₐ[K] SeparableClosure K) :
    ∃ g : AbsoluteGaloisGroup K, g.toAlgHom.comp σ = f := by
  let _ : Algebra L (SeparableClosure K) := σ.toRingHom.toAlgebra
  have : IsScalarTower K L (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x => (σ.commutes x).symm
  refine ⟨AlgEquiv.ofBijective (f.liftNormal (SeparableClosure K))
    (AlgHom.normal_bijective K (SeparableClosure K) (SeparableClosure K) _),
    AlgHom.ext fun x => ?_⟩
  simpa [RingHom.algebraMap_toAlgebra] using f.liftNormal_commutes (SeparableClosure K) x

variable [FiniteDimensional K L]

/-! ### The cosets of the subgroup cut out by `σ` -/

/-- **Two automorphisms of `Kˢ` agree on `σ(L)` exactly when they lie in the same coset** of the
subgroup `Gal(Kˢ/σ(L))` cut out by `σ`. -/
theorem algHom_comp_eq_iff_quotientGroup_mk_eq {g₁ g₂ : AbsoluteGaloisGroup K} :
    g₁.toAlgHom.comp σ = g₂.toAlgHom.comp σ ↔
      (QuotientGroup.mk g₁ : AbsoluteGaloisGroup K ⧸ σ.fieldRange.fixingSubgroup) =
        QuotientGroup.mk g₂ := by
  rw [QuotientGroup.eq, ← galoisSubgroup_toSubgroup K L σ, OpenSubgroup.mem_toSubgroup,
    mem_galoisSubgroup_iff]
  refine ⟨fun h x => ?_, fun h => AlgHom.ext fun x => ?_⟩
  · have hx : g₁ (σ x) = g₂ (σ x) := congrArg (fun f : L →ₐ[K] SeparableClosure K => f x) h
    simpa [AlgEquiv.mul_apply] using congrArg g₁.symm hx.symm
  · simpa [AlgEquiv.mul_apply] using (congrArg g₁ (h x)).symm

/-- **The cosets of `Gal(Kˢ/σ(L))` are the `K`-embeddings of `L` into `Kˢ`**, the coset of
`g` corresponding to `g ∘ σ`. Composed with `galoisSubgroup_index` it is the statement that a
finite separable extension of degree `d` has exactly `d` embeddings into a separable closure. -/
def fixingSubgroupQuotientEquivAlgHom :
    AbsoluteGaloisGroup K ⧸ σ.fieldRange.fixingSubgroup ≃ (L →ₐ[K] SeparableClosure K) :=
  Equiv.ofBijective
    (fun q => Quotient.liftOn' q (fun g : AbsoluteGaloisGroup K => g.toAlgHom.comp σ)
      fun _ _ h => algHom_comp_eq_iff_quotientGroup_mk_eq K L σ |>.2 (Quotient.sound h))
    ⟨by
      refine fun q q' => Quotient.inductionOn₂' q q' fun g g' h => ?_
      exact (algHom_comp_eq_iff_quotientGroup_mk_eq K L σ).1 h,
      fun f => by
        obtain ⟨g, hg⟩ := exists_algHom_comp_eq K L σ f
        exact ⟨QuotientGroup.mk g, hg⟩⟩

/-- `fixingSubgroupQuotientEquivAlgHom` sends the coset of `g` to `g ∘ σ`. -/
@[simp]
theorem fixingSubgroupQuotientEquivAlgHom_mk (g : AbsoluteGaloisGroup K) :
    fixingSubgroupQuotientEquivAlgHom K L σ (QuotientGroup.mk g) = g.toAlgHom.comp σ :=
  (rfl)

/-! ### The norm as a product of conjugates -/

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **The norm of `L/K` is the product of the conjugates of `σ`** (NSW, Ch. I §5): for any system
`t` of representatives of the cosets of `Gal(Kˢ/σ(L))`, the image of `N_{L/K} b` in `Kˢ`
is `∏ u, t u (σ b)`. The cosets index the `K`-embeddings of `L` into `Kˢ` through
`fixingSubgroupQuotientEquivAlgHom`, and `L/K` is separable, so Mathlib's
`Algebra.norm_eq_prod_embeddings` computes the product. -/
theorem algebraMap_norm_eq_prod_transversal
    (t : AbsoluteGaloisGroup K ⧸ σ.fieldRange.fixingSubgroup → AbsoluteGaloisGroup K)
    (ht : ∀ u, (QuotientGroup.mk (t u) :
      AbsoluteGaloisGroup K ⧸ σ.fieldRange.fixingSubgroup) = u) (b : L) :
    algebraMap K (SeparableClosure K) (Algebra.norm K b) = ∏ u, t u (σ b) := by
  have := algebra_isSeparable_of_algHom_separableClosure K L σ
  have hsplits : ∀ x : L, ((minpoly K x).map
      (algebraMap K (SeparableClosure K))).Splits := fun x =>
    IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable K x)
  refine (algebraMap (SeparableClosure K) (AlgebraicClosure K)).injective ?_
  rw [map_prod, ← IsScalarTower.algebraMap_apply K (SeparableClosure K) (AlgebraicClosure K),
    Algebra.norm_eq_prod_embeddings (K := K) (L := L) (E := AlgebraicClosure K) b]
  refine (Fintype.prod_equiv ((fixingSubgroupQuotientEquivAlgHom K L σ).trans
    (IntermediateField.algHomEquivAlgHomOfSplits (AlgebraicClosure K)
      (separableClosure K (AlgebraicClosure K)) hsplits)) _ _ fun u => ?_).symm
  have hu : fixingSubgroupQuotientEquivAlgHom K L σ u = (t u).toAlgHom.comp σ := by
    conv_lhs => rw [← ht u]
    rw [fixingSubgroupQuotientEquivAlgHom_mk]
  rw [Equiv.trans_apply, hu, IntermediateField.algHomEquivAlgHomOfSplits_apply_apply,
    AlgHom.comp_apply]
  -- `SeparableClosure K` is by definition `separableClosure K (AlgebraicClosure K)`, and only
  -- that abbreviation separates the two sides.
  rfl

end TauCeti
