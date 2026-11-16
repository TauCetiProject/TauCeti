/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import TauCeti.Order.Filter.AtTopBot.Finset
import TauCeti.Topology.Algebra.InfiniteSum.Sigma

/-!
# Uniform and locally uniform reindexing and finite-fibre regrouping

Extensions of Mathlib's `Mathlib.Topology.Algebra.InfiniteSum.UniformOn` and
`TauCeti.Topology.Algebra.InfiniteSum.Sigma` for infinite products and sums converging uniformly or
locally uniformly on a set:

* `HasProdUniformlyOn.sigma_of_finite` / `HasSumUniformlyOn.sigma_of_finite`: regrouping along
  finite fibres preserves uniform convergence to the same limit function, wrapping
  `HasProd.sigma_of_finite` via `UniformOnFun.ofFun_prod`.
* `HasProdLocallyUniformlyOn.sigma_of_finite` / `HasSumLocallyUniformlyOn.sigma_of_finite`:
  regrouping along finite fibres preserves locally uniform convergence to the same limit function
  via `TauCeti.tendsto_finset_sigma_univ_atTop`.
* `Equiv.hasProdUniformlyOn_iff` / `Equiv.hasSumUniformlyOn_iff` and
  `Equiv.hasProdLocallyUniformlyOn_iff` / `Equiv.hasSumLocallyUniformlyOn_iff`: reindexing by an
  equivalence preserves uniform and locally uniform convergence to the same limit function.
-/

public section

open Filter Finset

/-- **Regrouping a uniformly convergent product along finite fibres.** If a family over a sigma
type with finite fibres has product `g` uniformly on `s`, then so does the family of its fibre
products. -/
@[to_additive /-- **Regrouping a uniformly convergent series along finite fibres.** If a family
over a sigma type with finite fibres sums to `g` uniformly on `s`, then so does the family of its
fibre sums. -/]
theorem HasProdUniformlyOn.sigma_of_finite {ι β α : Type*} {γ : ι → Type*}
    [CommMonoid α] [UniformSpace α] [∀ i, Fintype (γ i)]
    {f : (Σ i, γ i) → β → α} {g : β → α} {s : Set β}
    (h : HasProdUniformlyOn f g s) :
    HasProdUniformlyOn (fun i x ↦ ∏ c, f ⟨i, c⟩ x) g s := by
  simpa [HasProdUniformlyOn, Function.comp_def, ← UniformOnFun.ofFun_prod, Finset.prod_fn] using
    HasProd.sigma_of_finite h

/-- **Regrouping a locally uniformly convergent product along finite fibres.** If a family over a
sigma type with finite fibres has product `g` locally uniformly on `s`, then so does the family of
its fibre products. -/
@[to_additive /-- **Regrouping a locally uniformly convergent series along finite fibres.** If a
family over a sigma type with finite fibres sums to `g` locally uniformly on `s`, then so does the
family of its fibre sums. -/]
theorem HasProdLocallyUniformlyOn.sigma_of_finite {ι β α : Type*} {γ : ι → Type*}
    [CommMonoid α] [UniformSpace α] [TopologicalSpace β] [∀ i, Fintype (γ i)]
    {f : (Σ i, γ i) → β → α} {g : β → α} {s : Set β}
    (h : HasProdLocallyUniformlyOn f g s) :
    HasProdLocallyUniformlyOn (fun i x ↦ ∏ c, f ⟨i, c⟩ x) g s := by
  classical
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h ⊢
  intro u hu x hx
  obtain ⟨t, ht, htu⟩ := h u hu x hx
  refine ⟨t, ht, ?_⟩
  filter_upwards [TauCeti.tendsto_finset_sigma_univ_atTop.eventually htu] with S hS y hy
  simpa only [Finset.prod_sigma] using hS y hy

/-- Reindexing a family by an equivalence preserves uniform convergence of its infinite product to
the same limit function. -/
@[to_additive /-- Reindexing a family by an equivalence preserves uniform convergence of its
infinite sum to the same limit function. -/]
theorem Equiv.hasProdUniformlyOn_iff {ι κ β α : Type*} [CommMonoid α] [UniformSpace α]
    (e : κ ≃ ι) {f : ι → β → α} {g : β → α} {s : Set β} :
    HasProdUniformlyOn (f ∘ e) g s ↔ HasProdUniformlyOn f g s := by
  simpa [HasProdUniformlyOn, Function.comp_assoc] using
    e.hasProd_iff (f := UniformOnFun.ofFun {s} ∘ f) (a := UniformOnFun.ofFun {s} g)

@[to_additive]
private theorem hasProdLocallyUniformlyOn_comp_equiv {ι κ β α : Type*} [CommMonoid α]
    [UniformSpace α] [TopologicalSpace β] (e : κ ≃ ι) {f : ι → β → α} {g : β → α} {s : Set β}
    (h : HasProdLocallyUniformlyOn f g s) :
    HasProdLocallyUniformlyOn (f ∘ e) g s := by
  have hmap : Tendsto (fun S : Finset κ ↦ S.map e.toEmbedding) atTop atTop :=
    tendsto_atTop_atTop.2 fun T ↦ ⟨T.map e.symm.toEmbedding, fun S hS i hi ↦
      Finset.mem_map.2 ⟨e.symm i, hS (Finset.mem_map.2 ⟨i, hi, rfl⟩), e.apply_symm_apply i⟩⟩
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h ⊢
  intro u hu x hx
  obtain ⟨t, ht, htu⟩ := h u hu x hx
  refine ⟨t, ht, ?_⟩
  filter_upwards [hmap.eventually htu] with S hS y hy
  simpa only [Function.comp_apply, Finset.prod_map, Equiv.coe_toEmbedding] using hS y hy

/-- Reindexing a family by an equivalence preserves locally uniform convergence of its infinite
product to the same limit function. -/
@[to_additive /-- Reindexing a family by an equivalence preserves locally uniform convergence of its
infinite sum to the same limit function. -/]
theorem Equiv.hasProdLocallyUniformlyOn_iff {ι κ β α : Type*} [CommMonoid α] [UniformSpace α]
    [TopologicalSpace β] (e : κ ≃ ι) {f : ι → β → α} {g : β → α} {s : Set β} :
    HasProdLocallyUniformlyOn (f ∘ e) g s ↔ HasProdLocallyUniformlyOn f g s :=
  ⟨fun h ↦ by
      simpa [Function.comp_assoc] using hasProdLocallyUniformlyOn_comp_equiv e.symm h,
    hasProdLocallyUniformlyOn_comp_equiv e⟩
