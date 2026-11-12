/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Topology

/-!
# Completed external products of completed combinations

For potentials `F₁ : S₁ → ℝ` and `F₂ : S₂ → ℝ`, the completed combinations of pairs with the
potential `F₁ p₁ + F₂ p₂` play the role of the completed tensor product of `NovikovModule R F₁`
and `NovikovModule R F₂`. The *external product* `a ⊠ b` of completed combinations has
coefficient `a(p₁) b(p₂)` at `(p₁, p₂)` (`TauCeti.NovikovModule.externalProduct`). It is jointly
continuous and shifts potential cutoffs additively. The universal property below is what
identifies it as a completed tensor product.

A linear map `f` of completed combinations *has potential shift `C`* if it sends every subgroup
`U_D` of `TauCeti.RingTheory.NovikovModule.Topology` into `U_(D + C)`; for a bilinear map the
condition reads `B(U_(D₁), U_(D₂)) ⊆ U_(D₁ + D₂ + C)`. By
`TauCeti.NovikovModule.kernelMap_toKernel` and
`TauCeti.NovikovModule.kernelProduct_toProductKernel` these are exactly the maps given by
supported kernels.

The external product has the universal property of a completed tensor product for such maps.
A bilinear map `B` with potential shift `C` factors as `B a b = lift B (a ⊠ b)` through a linear
map `NovikovModule.lift B` with the same potential shift, and `lift B` is the only continuous
linear map of completed combinations with this property (`NovikovModule.lift_externalProduct`,
`NovikovModule.lift_unique`). Consequently a pair of linear maps with potential shifts induces a
map `NovikovModule.map f g` of completed external products with `map f g (a ⊠ b) = f a ⊠ g b`,
and this construction is functorial. Tensor differentials `d ⊗ 1 ± 1 ⊗ d` of completed Floer and
Novikov complexes, and chain homotopies defined on them, are maps of this kind, so the identities
between them can be checked on external products of generators.

No discreteness or injectivity of the potentials is assumed. Uniqueness comes from density of
finite combinations (`TauCeti.NovikovModule.addHom_ext`): continuous additive maps from completed
combinations of pairs to any Hausdorff space are equal once they agree on external products
(`TauCeti.NovikovModule.ext_externalProduct`).

## Main definitions

* `TauCeti.NovikovModule.externalProduct`: the completed external product `a ⊠ b`.
* `TauCeti.NovikovModule.lift`: the linear map on completed external products induced by a
  bilinear map with potential shift.
* `TauCeti.NovikovModule.map`: the external product of two linear maps with potential shifts.

## Main results

* `TauCeti.NovikovModule.lift_externalProduct`, `TauCeti.NovikovModule.lift_unique`: the universal
  property of the completed external product.
* `TauCeti.NovikovModule.ext_externalProduct`: continuous additive maps agreeing on external
  products are equal.
* `TauCeti.NovikovModule.map_externalProduct`, `TauCeti.NovikovModule.map_comp_map`,
  `TauCeti.NovikovModule.map_id`: functoriality of external products of maps.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2, on completed modules over Novikov rings.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product.
-/

public section

noncomputable section

open Function

namespace TauCeti

namespace NovikovModule

section ExternalProduct

variable {R S₁ S₂ S₀ : Type*} {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ} {C : ℝ}

section CommSemiring

variable [CommSemiring R]

/-- The completed external product of completed combinations: `a ⊠ b` has coefficient
`a(p₁) b(p₂)` at the pair `(p₁, p₂)`, for the potential `F₁ p₁ + F₂ p₂` on pairs. -/
def externalProduct : NovikovModule R F₁ →ₗ[R] NovikovModule R F₂ →ₗ[R]
    NovikovModule R (fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2) :=
  LinearMap.mk₂ R (fun a b => ⟨fun q => a.val q.1 * b.val q.2, mem_iff.2 fun T =>
      (finite_setOf_le_add a b T).subset fun _ hq =>
        ⟨left_ne_zero_of_mul hq.1, right_ne_zero_of_mul hq.1, hq.2.le⟩⟩)
    (fun _ _ _ => Subtype.ext <| funext fun _ => add_mul _ _ _)
    (fun _ _ _ => Subtype.ext <| funext fun _ => mul_assoc _ _ _)
    (fun _ _ _ => Subtype.ext <| funext fun _ => mul_add _ _ _)
    (fun _ _ _ => Subtype.ext <| funext fun _ => mul_left_comm _ _ _)

/-- The coefficient of the external product at a pair is the product of the coefficients. -/
@[simp]
theorem externalProduct_apply_val (a : NovikovModule R F₁) (b : NovikovModule R F₂)
    (q : S₁ × S₂) : (externalProduct a b).val q = a.val q.1 * b.val q.2 :=
  (rfl)

/-- The external product of two single-generator combinations is the single-generator
combination at the pair, with the product coefficient. -/
@[simp]
theorem externalProduct_ofFinsupp_single (p₁ : S₁) (p₂ : S₂) (r₁ r₂ : R) :
    externalProduct (ofFinsupp F₁ (Finsupp.single p₁ r₁)) (ofFinsupp F₂ (Finsupp.single p₂ r₂)) =
      ofFinsupp _ (Finsupp.single (p₁, p₂) (r₁ * r₂)) := by
  classical
  ext ⟨q₁, q₂⟩
  simp only [externalProduct_apply_val, ofFinsupp_apply_val, Finsupp.single_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- A supported product kernel, viewed as a one-input kernel on pairs, maps external products to
kernel products. -/
theorem kernelMap_externalProduct {n : S₁ → S₂ → S₀ → R}
    (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
    (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀) (a : NovikovModule R F₁)
    (b : NovikovModule R F₂) :
    kernelMap (m := fun q : S₁ × S₂ => n q.1 q.2) (fun q => hn q.1 q.2) (fun q => hfin q.1 q.2)
      (externalProduct a b) = kernelProduct hn hfin a b :=
  Subtype.ext <| funext fun p₀ => by
    simp only [kernelMap_apply_val, externalProduct_apply_val, kernelProduct_apply_val]

end CommSemiring

section CommRing

variable [CommRing R]

/-- The external product shifts potential cutoffs additively: if `a` vanishes above `D₁` and `b`
vanishes above `D₂`, then `a ⊠ b` vanishes above `D₁ + D₂`. -/
theorem externalProduct_mem_potentialFiltration {D₁ D₂ : ℝ} {a : NovikovModule R F₁}
    {b : NovikovModule R F₂} (ha : a ∈ potentialFiltration R F₁ D₁)
    (hb : b ∈ potentialFiltration R F₂ D₂) :
    externalProduct a b ∈ potentialFiltration R _ (D₁ + D₂) :=
  mem_potentialFiltration.2 fun q hq => by
  rw [externalProduct_apply_val]
  rcases lt_or_ge D₁ (F₁ q.1) with h | h
  · rw [mem_potentialFiltration.1 ha _ h, zero_mul]
  · rw [mem_potentialFiltration.1 hb _ (by linarith), mul_zero]

/-- The external product, as a bilinear map with potential shift `0`. -/
private theorem externalProduct_mem_potentialFiltration_add_zero (D₁ D₂ : ℝ)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) (ha : a ∈ potentialFiltration R F₁ D₁)
    (hb : b ∈ potentialFiltration R F₂ D₂) :
    externalProduct a b ∈ potentialFiltration R _ (D₁ + D₂ + 0) := by
  simpa only [add_zero] using externalProduct_mem_potentialFiltration ha hb

/-- The external product is jointly continuous for the potential-cutoff topologies. -/
@[fun_prop]
theorem continuous_externalProduct :
    Continuous fun p : NovikovModule R F₁ × NovikovModule R F₂ => externalProduct p.1 p.2 := by
  simpa only [kernelProduct_toProductKernel externalProduct_mem_potentialFiltration_add_zero]
    using continuous_kernelProduct
      (potential_le_of_toProductKernel_ne_zero externalProduct_mem_potentialFiltration_add_zero)
      (toProductKernel_mem externalProduct)

/-- **Uniqueness on completed external products.** Continuous additive maps from completed
combinations of pairs to a Hausdorff space are equal if they agree on all external products. -/
theorem ext_externalProduct {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [T2Space M]
    {f g : NovikovModule R (fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2) →+ M}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ a b, f (externalProduct a b) = g (externalProduct a b)) : f = g :=
  addHom_ext hf hg fun q r => by
    rw [← mul_one r, ← externalProduct_ofFinsupp_single q.1 q.2 r 1]
    exact h _ _

section Lift

variable (B : NovikovModule R F₁ →ₗ[R] NovikovModule R F₂ →ₗ[R] NovikovModule R F₀)
  (hB : ∀ D₁ D₂ a b, a ∈ potentialFiltration R F₁ D₁ → b ∈ potentialFiltration R F₂ D₂ →
    B a b ∈ potentialFiltration R F₀ (D₁ + D₂ + C))

/-- The linear map on completed external products induced by a bilinear map `B` with potential
shift `C`: the kernel map of the coefficients of `B`, viewed as a one-input kernel on pairs. -/
def lift : NovikovModule R (fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2) →ₗ[R] NovikovModule R F₀ :=
  kernelMap (m := fun q : S₁ × S₂ => toProductKernel B q.1 q.2)
    (fun q => potential_le_of_toProductKernel_ne_zero hB q.1 q.2)
    (fun q => toProductKernel_mem B q.1 q.2)

/-- The coefficient of `lift B` at an output generator is the sum of the coefficients of `B`
weighted by the coefficients of the input. -/
theorem lift_apply_val (c : NovikovModule R (fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2)) (p₀ : S₀) :
    (lift B hB c).val p₀ = ∑ᶠ q : S₁ × S₂, c.val q * toProductKernel B q.1 q.2 p₀ := by
  rw [lift, kernelMap_apply_val]

/-- **The universal property of the completed external product.** A bilinear map with potential
shift factors through the external product. -/
@[simp]
theorem lift_externalProduct (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    lift B hB (externalProduct a b) = B a b := by
  rw [lift, kernelMap_externalProduct (potential_le_of_toProductKernel_ne_zero hB)
    (toProductKernel_mem B), kernelProduct_toProductKernel hB]

/-- The induced map on completed external products has the same potential shift as `B`. -/
theorem lift_mem_potentialFiltration {D : ℝ}
    {c : NovikovModule R (fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2)}
    (hc : c ∈ potentialFiltration R _ D) : lift B hB c ∈ potentialFiltration R F₀ (D + C) :=
  kernelMap_mem_potentialFiltration _ _ hc

/-- The induced map on completed external products is continuous. -/
@[fun_prop]
theorem continuous_lift : Continuous (lift B hB) :=
  continuous_kernelMap _ _

/-- **Uniqueness in the universal property.** The induced map is the only continuous linear map
from completed external products to `NovikovModule R F₀` that factors `B`. -/
theorem lift_unique {f : NovikovModule R (fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2) →ₗ[R]
      NovikovModule R F₀} (hf : Continuous f)
    (h : ∀ a b, f (externalProduct a b) = B a b) : f = lift B hB :=
  LinearMap.toAddMonoidHom_injective <| ext_externalProduct hf (continuous_lift B hB) fun a b => by
    simp only [LinearMap.toAddMonoidHom_coe, h, lift_externalProduct]

end Lift

section Map

variable {T₁ T₂ T₁' T₂' : Type*} {G₁ : T₁ → ℝ} {G₂ : T₂ → ℝ} {G₁' : T₁' → ℝ} {G₂' : T₂' → ℝ}
  {C₁ C₂ C₁' C₂' : ℝ}
  (f : NovikovModule R F₁ →ₗ[R] NovikovModule R G₁)
  (g : NovikovModule R F₂ →ₗ[R] NovikovModule R G₂)
  (hf : ∀ D a, a ∈ potentialFiltration R F₁ D → f a ∈ potentialFiltration R G₁ (D + C₁))
  (hg : ∀ D b, b ∈ potentialFiltration R F₂ D → g b ∈ potentialFiltration R G₂ (D + C₂))

include hf hg in
/-- The external product of two maps with potential shifts `C₁` and `C₂` is a bilinear map with
potential shift `C₁ + C₂`. -/
private theorem externalProduct_compl₁₂_mem_potentialFiltration (D₁ D₂ : ℝ)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) (ha : a ∈ potentialFiltration R F₁ D₁)
    (hb : b ∈ potentialFiltration R F₂ D₂) :
    externalProduct.compl₁₂ f g a b ∈ potentialFiltration R _ (D₁ + D₂ + (C₁ + C₂)) :=
  monotone_potentialFiltration (le_of_eq (by ring))
    (externalProduct_mem_potentialFiltration (hf _ _ ha) (hg _ _ hb))

/-- The external product of two linear maps with potential shifts, as a linear map of completed
external products. -/
def map : NovikovModule R (fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2) →ₗ[R]
    NovikovModule R (fun q : T₁ × T₂ => G₁ q.1 + G₂ q.2) :=
  lift (externalProduct.compl₁₂ f g) (externalProduct_compl₁₂_mem_potentialFiltration f g hf hg)

/-- The external product of two maps sends `a ⊠ b` to `f a ⊠ g b`. -/
@[simp]
theorem map_externalProduct (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    map f g hf hg (externalProduct a b) = externalProduct (f a) (g b) :=
  lift_externalProduct _ _ a b

/-- The external product of maps with potential shifts `C₁` and `C₂` has potential shift
`C₁ + C₂`. -/
theorem map_mem_potentialFiltration {D : ℝ}
    {c : NovikovModule R (fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2)}
    (hc : c ∈ potentialFiltration R _ D) :
    map f g hf hg c ∈ potentialFiltration R _ (D + (C₁ + C₂)) :=
  lift_mem_potentialFiltration _ _ hc

/-- The external product of two maps is continuous. -/
@[fun_prop]
theorem continuous_map : Continuous (map f g hf hg) :=
  continuous_lift _ _

/-- The external product of two maps is the only continuous linear map of completed external
products sending each `a ⊠ b` to `f a ⊠ g b`. -/
theorem map_unique {φ : NovikovModule R (fun q : S₁ × S₂ => F₁ q.1 + F₂ q.2) →ₗ[R]
      NovikovModule R (fun q : T₁ × T₂ => G₁ q.1 + G₂ q.2)} (hφ : Continuous φ)
    (h : ∀ a b, φ (externalProduct a b) = externalProduct (f a) (g b)) : φ = map f g hf hg :=
  lift_unique _ _ hφ h

/-- External products of maps compose factorwise. -/
theorem map_comp_map (f' : NovikovModule R G₁ →ₗ[R] NovikovModule R G₁')
    (g' : NovikovModule R G₂ →ₗ[R] NovikovModule R G₂')
    (hf' : ∀ D a, a ∈ potentialFiltration R G₁ D → f' a ∈ potentialFiltration R G₁' (D + C₁'))
    (hg' : ∀ D b, b ∈ potentialFiltration R G₂ D → g' b ∈ potentialFiltration R G₂' (D + C₂')) :
    map f' g' hf' hg' ∘ₗ map f g hf hg =
      map (f' ∘ₗ f) (g' ∘ₗ g) (comp_mem_potentialFiltration_add hf hf')
        (comp_mem_potentialFiltration_add hg hg') :=
  map_unique _ _ _ _ ((continuous_map f' g' hf' hg').comp (continuous_map f g hf hg))
    fun a b => by simp

end Map

/-- The external product of identity maps is the identity. -/
@[simp]
theorem map_id :
    map (LinearMap.id : NovikovModule R F₁ →ₗ[R] _) (LinearMap.id : NovikovModule R F₂ →ₗ[R] _)
      (C₁ := 0) (C₂ := 0) (fun D a ha => by simpa using ha) (fun D b hb => by simpa using hb) =
      LinearMap.id :=
  (map_unique _ _ _ _ continuous_id fun _ _ => rfl).symm

end CommRing

end ExternalProduct

end NovikovModule

end TauCeti
