/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.FieldTheory.Normal.Embeddings
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# The norm of a finite subextension as a product over the absolute Galois group

Let `K` be a field, `Kˢ` a separable closure, `L/K` a finite extension and `σ : L →ₐ[K] Kˢ` a
`K`-embedding. Composing with `σ` identifies the coset space of the open subgroup
`Gal(Kˢ/σ(L))` cut out by `σ` with the set of `K`-embeddings of `L` into `Kˢ`,

```text
G_K ⧸ Gal(Kˢ/σ(L)) ≃ (L →ₐ[K] Kˢ),    g ↦ g ∘ σ,
```

which is `TauCeti.FieldTheory.fixingSubgroupQuotientEquivAlgHom` for the normal extension
`Kˢ / K`. Under that identification the classical formula "the norm is the product of the
conjugates" becomes a product over a system `t` of coset representatives:

```text
algebraMap K Kˢ (N_{L/K} b) = ∏ u : G_K ⧸ Gal(Kˢ/σ(L)), t u (σ b).
```

This is the shape in which the norm of a finite extension meets the cohomology of `G_K`, where a
sum `x ↦ ∑ u, t u • x` over a transversal is the standard degree-zero corestriction: on units of
`Kˢ` fixed by `Gal(Kˢ/σ(L))`, that sum is the norm of `L/K`.

Separability of `L/K` is not assumed. An embedding of `L` into a separable closure of `K` forces
it by Mathlib's `Algebra.IsSeparable.of_algHom`. Finiteness of `L/K` is used twice: it bounds the
index of `Gal(Kˢ/σ(L))` by `[L : K]`, so that the coset space is a finite index set, and it is the
hypothesis of Mathlib's product formula for the norm, `Algebra.norm_eq_prod_embeddings`.

The same holds relatively. For open subgroups `W` and `W'` of `G_K` with fixed fields `E ⊆ E'`,
the cosets of `W'` in `W` are the `E`-embeddings of `E'` into `Kˢ`, so the norm of `E'/E` is the
product of the translates by representatives of these cosets. This is the form in which the norm
`x ↦ ∑ q, q.out • x` between the levels of `W'` and `W` of a discrete `G_K`-module is compared with
the norm of the extension `E'/E`.

## Main results

* `TauCeti.algebraMap_norm_eq_prod_transversal`: the norm of `L/K` is the product of the
  conjugates of `σ`, indexed by a transversal of `Gal(Kˢ/σ(L))`.
* `TauCeti.coe_norm_eq_prod_quotient_out`: the norm of `E'/E` is the product of the translates by
  representatives of the cosets of `W'` in `W`.

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

variable [FiniteDimensional K L]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **The norm of `L/K` is the product of the conjugates of `σ`** (NSW, Ch. I §5): for any system
`t` of representatives of the cosets of `Gal(Kˢ/σ(L))`, the image of `N_{L/K} b` in `Kˢ`
is `∏ u, t u (σ b)`. -/
theorem algebraMap_norm_eq_prod_transversal
    (t : AbsoluteGaloisGroup K ⧸ σ.fieldRange.fixingSubgroup → AbsoluteGaloisGroup K)
    (ht : ∀ u, (QuotientGroup.mk (t u) :
      AbsoluteGaloisGroup K ⧸ σ.fieldRange.fixingSubgroup) = u) (b : L) :
    algebraMap K (SeparableClosure K) (Algebra.norm K b) = ∏ u, t u (σ b) := by
  have := Algebra.IsSeparable.of_algHom K (SeparableClosure K) σ
  have hsplits : ∀ x : L, ((minpoly K x).map
      (algebraMap K (SeparableClosure K))).Splits := fun x =>
    IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable K x)
  refine (algebraMap (SeparableClosure K) (AlgebraicClosure K)).injective ?_
  rw [map_prod, ← IsScalarTower.algebraMap_apply K (SeparableClosure K) (AlgebraicClosure K),
    Algebra.norm_eq_prod_embeddings (K := K) (L := L) (E := AlgebraicClosure K) b]
  refine (Fintype.prod_equiv ((FieldTheory.fixingSubgroupQuotientEquivAlgHom σ).trans
    (Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits (AlgebraicClosure K) (SeparableClosure K)
      hsplits)) _ _ fun u => ?_).symm
  have hu : FieldTheory.fixingSubgroupQuotientEquivAlgHom σ u = (t u).toAlgHom.comp σ := by
    conv_lhs => rw [← ht u]
    rw [FieldTheory.fixingSubgroupQuotientEquivAlgHom_mk]
  rw [Equiv.trans_apply, hu, Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]

section Relative

variable {K} {E E' : IntermediateField K (SeparableClosure K)} [Algebra E E']
  [IsScalarTower E E' (SeparableClosure K)] [FiniteDimensional E E']
  {W W' : OpenSubgroup (AbsoluteGaloisGroup K)}

omit σ [FiniteDimensional K L] in
/-- **The relative norm of `E'/E` is the product of the conjugates over `G_E`**: if `W` and `W'`
are open subgroups of `G_K` with fixed fields `E ⊆ E'`, then the norm `N_{E'/E} x`, read in `Kˢ`,
is the product of the translates of `x` by representatives of the cosets of `W'` in `W`. The
extension `E'/E` need not be normal. -/
theorem coe_norm_eq_prod_quotient_out (hW : fixedField W.toSubgroup = E)
    (hW' : fixedField W'.toSubgroup = E') (x : E') :
    ((Algebra.norm E x : E) : SeparableClosure K) =
      ∏ q : W.toSubgroup ⧸ W'.toSubgroup.subgroupOf W.toSubgroup,
        (q.out : AbsoluteGaloisGroup K) (x : SeparableClosure K) := by
  let φ := IsScalarTower.toAlgHom E E' (SeparableClosure K)
  have : IsGalois E (SeparableClosure K) := IsGalois.tower_top_of_isGalois K E _
  have := Algebra.IsSeparable.of_algHom E (SeparableClosure K) φ
  have hsplits : ∀ y : E', ((minpoly E y).map (algebraMap E (SeparableClosure K))).Splits :=
    fun y => IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable E y)
  -- `W` is `Gal(Kˢ/E)`, and under this identification `W'` is the subgroup fixing `φ(E') = E'`.
  let e : W.toSubgroup ≃* (SeparableClosure K ≃ₐ[E] SeparableClosure K) :=
    (MulEquiv.subgroupCongr (toSubgroup_eq_fixingSubgroup_of_fixedField_eq hW)).trans
      E.fixingSubgroupEquiv
  have he (g : W.toSubgroup) (y : SeparableClosure K) : e g y = (g : AbsoluteGaloisGroup K) y := by
    rw [MulEquiv.trans_apply, IntermediateField.coe_fixingSubgroupEquiv_apply,
      MulEquiv.subgroupCongr_apply]
  have hmem (g : W.toSubgroup) :
      g ∈ W'.toSubgroup.subgroupOf W.toSubgroup ↔ e g ∈ φ.fieldRange.fixingSubgroup := by
    rw [Subgroup.mem_subgroupOf, toSubgroup_eq_fixingSubgroup_of_fixedField_eq hW',
      IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
    refine ⟨fun h ↦ ?_, fun h y hy ↦ h y ⟨⟨y, hy⟩, rfl⟩⟩
    rintro _ ⟨y, rfl⟩
    exact h _ y.2
  -- The cosets of `W'` in `W` are the `E`-embeddings of `E'` in `Kˢ`, and those in an algebraic
  -- closure of `Kˢ`.
  let f : W.toSubgroup ⧸ W'.toSubgroup.subgroupOf W.toSubgroup ≃
      (E' →ₐ[E] AlgebraicClosure (SeparableClosure K)) := (Quotient.congr e.toEquiv fun a b ↦ by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hmem, map_mul, map_inv]
      -- `e.toEquiv` is `e` as a function.
      rfl).trans
    ((FieldTheory.fixingSubgroupQuotientEquivAlgHom φ).trans
      (Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits (AlgebraicClosure (SeparableClosure K))
        (SeparableClosure K) hsplits))
  refine (algebraMap (SeparableClosure K) (AlgebraicClosure (SeparableClosure K))).injective ?_
  rw [map_prod, ← IntermediateField.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply E (SeparableClosure K),
    Algebra.norm_eq_prod_embeddings (K := E) (L := E') (E := AlgebraicClosure (SeparableClosure K))]
  refine (Fintype.prod_equiv f _ _ fun q ↦ ?_).symm
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  -- `f` sends the coset of `g` to the embedding `e g ∘ φ`, read in the algebraic closure; the
  -- first step, the coset of `g` to the coset of `e g`, is `Quotient.congr` on a representative,
  -- and `e g` acts on `Kˢ` as `g` by `he`.
  rw [Equiv.trans_apply, Equiv.trans_apply,
    Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply]
  exact congrArg (algebraMap _ _) ((congrArg (· x)
    (FieldTheory.fixingSubgroupQuotientEquivAlgHom_mk φ (e q.out))).trans (he q.out x)).symm

end Relative

end TauCeti
