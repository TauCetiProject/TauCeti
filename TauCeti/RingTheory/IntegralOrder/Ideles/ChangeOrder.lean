/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IntegralOrder.Ideles.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Basic

/-!
# Changing the reference order of the idele group

Let `A` be a Dedekind domain with fraction field `F` and let `B` be an `F`-algebra. The finite
idele group `J_f(Λ)` of `TauCeti.OrderIdeles.FiniteIdeles` is the restricted product of the unit
groups `B_vˣ = (𝒪_v ⊗[A] B)ˣ` with respect to the unit groups `Λ_vˣ` of the completions of an
`A`-order `Λ` in `B`. This file shows that, up to a canonical isomorphism, this group depends
only on `B`: two orders `Λ` and `Γ` have the same completions at all but finitely many places
(`eventually_baseChange_eq`), so changing the reference order changes only finitely many of the
compact open factors `Λ_vˣ`, and the identity in every coordinate is an isomorphism
`J_f(Λ) ≃* J_f(Γ)` (`TauCeti.OrderIdeles.changeOrder`). It carries principal ideles to principal
ideles.

Inside the common group `J_f(B)` the unit subgroups `U_f(Λ)` of all orders can be compared: the
image of `U_f(Λ)` in `J_f(Γ)` consists of the ideles with every component in `Λ_vˣ`, so it lies in
`U_f(Γ)` when `Λ ≤ Γ`; correspondingly `I(α) ⊆ I_Γ(α)`. Over a number field `K` the same holds for
the full idele groups `J(Λ)`, whose archimedean factors do not involve the order.

## Main definitions

* `TauCeti.OrderIdeles.changeOrder`: the isomorphism `J_f(Λ) ≃* J_f(Γ)` for two orders.
* `TauCeti.OrderIdeles.Ideles.changeOrder`: the isomorphism `J(Λ) ≃* J(Γ)` over a number field.

## Main results

* `TauCeti.OrderIdeles.eventually_baseChange_eq`: two orders have the same completion at all but
  finitely many places.
* `TauCeti.OrderIdeles.changeOrder_principal`: changing the order preserves principal ideles.
* `TauCeti.OrderIdeles.unitIdeles_eq_integralSubgroup`: `U_f(Λ)` is the everywhere-integral
  subgroup of the restricted product `J_f(Λ)`.
* `TauCeti.OrderIdeles.map_unitIdeles_changeOrder`,
  `TauCeti.OrderIdeles.mem_map_unitIdeles_changeOrder`: the image of `U_f(Λ)` in `J_f(Γ)` is the
  subgroup of ideles with every component a unit of `Λ_v`.
* `TauCeti.OrderIdeles.map_unitIdeles_changeOrder_le`: for orders `Λ ≤ Γ`, `U_f(Λ) ≤ U_f(Γ)`.
* `TauCeti.OrderIdeles.lattice_le_lattice_changeOrder`: for orders `Λ ≤ Γ`, `I(α) ⊆ I_Γ(α)`.

## References

* A. Fröhlich, *Locally free modules over arithmetic orders*, J. Reine Angew. Math. 274/275
  (1975), 112–138, §2.
-/

public section

open TensorProduct IsDedekindDomain Submodule
open scoped RestrictedProduct

namespace TauCeti.OrderIdeles

open IntegralOrder

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  {B : Type*} [Ring B] [Algebra A B] [Algebra F B] [IsScalarTower A F B]
  {Λ Γ Δ : Subalgebra A B}

/-- **Orders agree almost everywhere.** Two `A`-orders in `B` have the same completion at all but
finitely many height-one primes of `A`. -/
theorem eventually_baseChange_eq (hΛ : IsOrder F Λ) (hΓ : IsOrder F Γ) :
    ∀ᶠ v : HeightOneSpectrum A in Filter.cofinite,
      Λ.baseChange (v.adicCompletionIntegers F) = Γ.baseChange (v.adicCompletionIntegers F) := by
  have hΛ' := isOrder_iff_isLattice.1 hΛ
  have hΓ' := isOrder_iff_isLattice.1 hΓ
  filter_upwards [eventually_baseChange_le hΛ'.fg hΓ'.span_eq_top,
    eventually_baseChange_le hΓ'.fg hΛ'.span_eq_top] with v h₁ h₂
  refine Subalgebra.toSubmodule_injective ?_
  rw [Subalgebra.toSubmodule_baseChange, Subalgebra.toSubmodule_baseChange]
  exact h₁.antisymm h₂

omit [Algebra F B] [IsScalarTower A F B] in
variable (F Λ) in
/-- `U_f(Λ)` is the everywhere-integral subgroup of the restricted product `J_f(Λ)`. -/
theorem unitIdeles_eq_integralSubgroup :
    unitIdeles F Λ =
      integralSubgroup fun v : HeightOneSpectrum A ↦
        (Λ.baseChange (v.adicCompletionIntegers F)).toSubmonoid.units :=
  Subgroup.ext fun α ↦ mem_unitIdeles.trans (mem_integralSubgroup _ α).symm

/-- **Changing the reference order.** For two `A`-orders `Λ` and `Γ` in `B`, the finite idele
groups `J_f(Λ)` and `J_f(Γ)` are the same restricted product of the `(𝒪_v ⊗[A] B)ˣ`, since the
completions of `Λ` and `Γ` differ at only finitely many places. This is the identity in every
coordinate. -/
noncomputable def changeOrder (hΛ : IsOrder F Λ) (hΓ : IsOrder F Γ) :
    FiniteIdeles F Λ ≃* FiniteIdeles F Γ :=
  restrictedProductCongr _ _ <| (eventually_baseChange_eq hΛ hΓ).mono fun _ hv ↦ by rw [hv]

@[simp]
theorem changeOrder_apply (hΛ : IsOrder F Λ) (hΓ : IsOrder F Γ) (α : FiniteIdeles F Λ)
    (v : HeightOneSpectrum A) : changeOrder hΛ hΓ α v = α v :=
  restrictedProductCongr_apply _ _ _ α v

@[simp]
theorem changeOrder_refl (hΛ : IsOrder F Λ) : changeOrder hΛ hΛ = MulEquiv.refl _ :=
  restrictedProductCongr_refl _

@[simp]
theorem changeOrder_symm (hΛ : IsOrder F Λ) (hΓ : IsOrder F Γ) :
    (changeOrder hΛ hΓ).symm = changeOrder hΓ hΛ :=
  restrictedProductCongr_symm _ _ _

@[simp]
theorem changeOrder_trans (hΛ : IsOrder F Λ) (hΓ : IsOrder F Γ) (hΔ : IsOrder F Δ) :
    (changeOrder hΛ hΓ).trans (changeOrder hΓ hΔ) = changeOrder hΛ hΔ :=
  restrictedProductCongr_trans _ _ _ _ _

/-- **Principal ideles do not depend on the order.** -/
@[simp]
theorem changeOrder_principal (hΛ : IsOrder F Λ) (hΓ : IsOrder F Γ) (b : Bˣ) :
    changeOrder hΛ hΓ (principal F Λ hΛ.span_eq_top b) = principal F Γ hΓ.span_eq_top b :=
  RestrictedProduct.ext _ _ fun v ↦ Units.ext (by simp)

/-- **The unit ideles of one order inside the ideles of another.** The image of `U_f(Λ)` in
`J_f(Γ)` is the subgroup of ideles whose every component is a unit of `Λ_v`. -/
theorem map_unitIdeles_changeOrder (hΛ : IsOrder F Λ) (hΓ : IsOrder F Γ) :
    (unitIdeles F Λ).map (changeOrder hΛ hΓ : FiniteIdeles F Λ →* FiniteIdeles F Γ) =
      integralSubgroupOf _ fun v : HeightOneSpectrum A ↦
        (Λ.baseChange (v.adicCompletionIntegers F)).toSubmonoid.units := by
  rw [unitIdeles_eq_integralSubgroup]
  exact map_integralSubgroup_restrictedProductCongr _ _ _

/-- An idele of `J_f(Γ)` comes from `U_f(Λ)` exactly when every component is a unit of `Λ_v`. -/
theorem mem_map_unitIdeles_changeOrder (hΛ : IsOrder F Λ) (hΓ : IsOrder F Γ)
    {α : FiniteIdeles F Γ} :
    α ∈ (unitIdeles F Λ).map (changeOrder hΛ hΓ) ↔
      ∀ v, α v ∈ (Λ.baseChange (v.adicCompletionIntegers F)).toSubmonoid.units := by
  rw [map_unitIdeles_changeOrder, mem_integralSubgroupOf]

/-- **Unit ideles grow with the order.** For orders `Λ ≤ Γ`, the image of `U_f(Λ)` in `J_f(Γ)` lies
in `U_f(Γ)`. -/
theorem map_unitIdeles_changeOrder_le (hΛ : IsOrder F Λ) (hΓ : IsOrder F Γ) (hle : Λ ≤ Γ) :
    (unitIdeles F Λ).map (changeOrder hΛ hΓ) ≤ unitIdeles F Γ := by
  rw [map_unitIdeles_changeOrder, unitIdeles_eq_integralSubgroup, ← integralSubgroupOf_self,
    integralSubgroupOf_le_integralSubgroupOf_iff]
  exact fun v ↦ Submonoid.units_mono fun _ hx ↦ Subalgebra.baseChange_mono _ hle hx

/-- **Lattices grow with the order.** For orders `Λ ≤ Γ`, the lattice `I(α)` of a finite idele
relative to `Λ` lies in its lattice relative to `Γ`. -/
theorem lattice_le_lattice_changeOrder (hΛ : IsOrder F Λ) (hΓ : IsOrder F Γ) (hle : Λ ≤ Γ)
    (α : FiniteIdeles F Λ) : lattice F Λ α ≤ lattice F Γ (changeOrder hΛ hΓ α) := fun x hx ↦
  mem_lattice_iff.2 fun v ↦ by
    simpa using Subalgebra.baseChange_mono _ hle (mem_lattice_iff.1 hx v)

end TauCeti.OrderIdeles

/-! ### Full ideles over a number field -/

namespace TauCeti.OrderIdeles.Ideles

open NumberField IntegralOrder

variable {K : Type*} [Field K] [NumberField K] {B : Type*} [Ring B] [Algebra K B]
  [Algebra (𝓞 K) B] [IsScalarTower (𝓞 K) K B] {Λ Γ Δ : Subalgebra (𝓞 K) B}

/-- **Changing the reference order of the full ideles.** For two `𝓞_K`-orders `Λ` and `Γ` in `B`,
the idele groups `J(Λ)` and `J(Γ)` agree: the archimedean factors do not involve the order, and the
finite parts are identified by `TauCeti.OrderIdeles.changeOrder`. -/
noncomputable def changeOrder (hΛ : IsOrder K Λ) (hΓ : IsOrder K Γ) : Ideles K Λ ≃* Ideles K Γ :=
  .prodCongr (.refl _) (OrderIdeles.changeOrder hΛ hΓ)

@[simp]
theorem changeOrder_fst (hΛ : IsOrder K Λ) (hΓ : IsOrder K Γ) (α : Ideles K Λ) :
    (changeOrder hΛ hΓ α).1 = α.1 :=
  (rfl)

@[simp]
theorem changeOrder_snd (hΛ : IsOrder K Λ) (hΓ : IsOrder K Γ) (α : Ideles K Λ) :
    (changeOrder hΛ hΓ α).2 = OrderIdeles.changeOrder hΛ hΓ α.2 :=
  (rfl)

@[simp]
theorem changeOrder_refl (hΛ : IsOrder K Λ) : changeOrder hΛ hΛ = MulEquiv.refl _ :=
  MulEquiv.ext fun α ↦ Prod.ext rfl <| by ext; simp

@[simp]
theorem changeOrder_symm (hΛ : IsOrder K Λ) (hΓ : IsOrder K Γ) :
    (changeOrder hΛ hΓ).symm = changeOrder hΓ hΛ :=
  MulEquiv.ext fun α ↦ (changeOrder hΛ hΓ).symm_apply_eq.2 <| Prod.ext rfl <| by ext; simp

@[simp]
theorem changeOrder_trans (hΛ : IsOrder K Λ) (hΓ : IsOrder K Γ) (hΔ : IsOrder K Δ) :
    (changeOrder hΛ hΓ).trans (changeOrder hΓ hΔ) = changeOrder hΛ hΔ :=
  MulEquiv.ext fun α ↦ Prod.ext rfl <| by ext; simp

/-- **Principal ideles do not depend on the order.** -/
@[simp]
theorem changeOrder_principal (hΛ : IsOrder K Λ) (hΓ : IsOrder K Γ) (b : Bˣ) :
    changeOrder hΛ hΓ (principal K Λ hΛ.span_eq_top b) = principal K Γ hΓ.span_eq_top b :=
  Prod.ext (funext fun _ ↦ Units.ext (by simp)) (by simp)

/-- **The unit ideles of one order inside the ideles of another.** The image of `U(Λ)` in `J(Γ)`
consists of the ideles whose every finite component is a unit of `Λ_v`. -/
theorem mem_map_unitIdeles_changeOrder (hΛ : IsOrder K Λ) (hΓ : IsOrder K Γ) {α : Ideles K Γ} :
    α ∈ (unitIdeles K Λ).map (changeOrder hΛ hΓ) ↔
      ∀ v, α.2 v ∈ (Λ.baseChange (v.adicCompletionIntegers K)).toSubmonoid.units := by
  rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.mem_comap, mem_unitIdeles]
  simp

/-- **Unit ideles grow with the order.** For orders `Λ ≤ Γ`, the image of `U(Λ)` in `J(Γ)` lies in
`U(Γ)`. -/
theorem map_unitIdeles_changeOrder_le (hΛ : IsOrder K Λ) (hΓ : IsOrder K Γ) (hle : Λ ≤ Γ) :
    (unitIdeles K Λ).map (MonoidHom.ofClass (changeOrder hΛ hΓ)) ≤ unitIdeles K Γ := fun _ hα ↦
  mem_unitIdeles.2 <| OrderIdeles.map_unitIdeles_changeOrder_le hΛ hΓ hle <|
    (OrderIdeles.mem_map_unitIdeles_changeOrder hΛ hΓ).2
      ((mem_map_unitIdeles_changeOrder hΛ hΓ).1 hα)

end TauCeti.OrderIdeles.Ideles
