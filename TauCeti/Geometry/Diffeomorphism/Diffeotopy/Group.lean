/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic

/-!
# The group of diffeotopies

The `C^n` diffeotopies `φ_t`, `t ∈ [0, 1]`, of a manifold `M` starting at the identity form a
group under the **pointwise product** `(φ ψ)_t = φ_t ∘ ψ_t`, with unit the constant diffeotopy
and inverse the pointwise inverse `φ_t⁻¹` (`TauCeti.Diffeotopy.instGroup`). This is the group of
paths from the identity in the diffeomorphism group of `M`, with the multiplication of that group
applied at each time. It matches the convention of the self-diffeomorphism group, where `f * g`
acts as `f ∘ g` (`Diffeomorph.mul_def`). In terms of the existing operations, `φ * ψ` is the
composite `ψ.trans φ` with slices `φ_t ∘ ψ_t`, and `φ⁻¹` is `φ.symm`. The pointwise product is
distinct from the concatenation of paths in time.

Taking the time slice at `t`, in particular the final diffeomorphism at `t = 1`, is a group
homomorphism to the self-diffeomorphism group (`TauCeti.Diffeotopy.timeSliceHom`,
`TauCeti.Diffeotopy.finalHom`). For a subgroup `S` of self-diffeomorphisms, the diffeotopies all of
whose time slices lie in `S` form a subgroup (`TauCeti.Diffeotopy.sliceSubgroup S`). For the
stabilizer of a symplectic form these are the symplectic isotopies starting at the identity.

## Main definitions

* `TauCeti.Diffeotopy.instGroup`: the group of diffeotopies under the pointwise product.
* `TauCeti.Diffeotopy.timeSliceHom`, `TauCeti.Diffeotopy.finalHom`: evaluation at a time as a
  group homomorphism.
* `TauCeti.Diffeotopy.sliceSubgroup S`: the diffeotopies all of whose time slices lie in `S`.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the group of symplectic isotopies and its pointwise
  product).
-/

public section

noncomputable section

namespace TauCeti

namespace Diffeotopy

open unitInterval
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The constant diffeotopy is the unit of the group of diffeotopies. -/
instance instOne : One (Diffeotopy J n M) where one := refl J n M

/-- The product `φ * ψ` of diffeotopies is the pointwise composite with slices `φ_t ∘ ψ_t`, that is
`ψ.trans φ`, matching the composition order of the self-diffeomorphism group. -/
instance instMul : Mul (Diffeotopy J n M) where mul Φ Ψ := Ψ.trans Φ

/-- The inverse of a diffeotopy is its pointwise inverse, with slices `φ_t⁻¹`. -/
instance instInv : Inv (Diffeotopy J n M) where inv Φ := Φ.symm

/-- **The group of diffeotopies** under the pointwise product `(φ ψ)_t = φ_t ∘ ψ_t`. -/
instance instGroup : Group (Diffeotopy J n M) where
  mul_assoc Φ Ψ Θ := (trans_assoc Θ Ψ Φ).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm

/-- The unit of the group of diffeotopies is the constant diffeotopy. -/
theorem one_def : (1 : Diffeotopy J n M) = refl J n M :=
  (rfl)

/-- The product `φ * ψ` of diffeotopies is the composite `ψ.trans φ`, with slices `φ_t ∘ ψ_t`. -/
theorem mul_def (Φ Ψ : Diffeotopy J n M) : Φ * Ψ = Ψ.trans Φ :=
  (rfl)

/-- The inverse of a diffeotopy is its pointwise inverse `Φ.symm`. -/
theorem inv_def (Φ : Diffeotopy J n M) : Φ⁻¹ = Φ.symm :=
  (rfl)

/-- The unit diffeotopy fixes every point at every time. -/
@[simp]
theorem one_apply (p : I × M) : (1 : Diffeotopy J n M) p = p.2 :=
  refl_apply p

/-- The product of diffeotopies applies `ψ` and then `φ` at the same time. -/
@[simp]
theorem mul_apply (Φ Ψ : Diffeotopy J n M) (p : I × M) : (Φ * Ψ) p = Φ (p.1, Ψ p) :=
  trans_apply Ψ Φ p

/-- The time slice of a product of diffeotopies is the product of the time slices. -/
@[simp]
theorem timeSlice_mul (Φ Ψ : Diffeotopy J n M) (t : I) :
    (Φ * Ψ).timeSlice t = Φ.timeSlice t * Ψ.timeSlice t :=
  timeSlice_trans Ψ Φ t

/-- The time slices of the unit diffeotopy are the identity. -/
@[simp]
theorem timeSlice_one (t : I) : (1 : Diffeotopy J n M).timeSlice t = 1 :=
  timeSlice_refl t

/-- The time slice of the inverse diffeotopy is the inverse time slice. -/
@[simp]
theorem timeSlice_inv (Φ : Diffeotopy J n M) (t : I) : Φ⁻¹.timeSlice t = (Φ.timeSlice t)⁻¹ :=
  timeSlice_symm Φ t

variable (J n M) in
/-- **Evaluation at a time is a homomorphism.** The time slice at `t` of the group of diffeotopies
in the self-diffeomorphism group. -/
def timeSliceHom (t : I) : Diffeotopy J n M →* M ≃ₘ^n⟮J, J⟯ M where
  toFun Φ := Φ.timeSlice t
  map_one' := timeSlice_one t
  map_mul' Φ Ψ := timeSlice_mul Φ Ψ t

@[simp]
theorem timeSliceHom_apply (t : I) (Φ : Diffeotopy J n M) :
    timeSliceHom J n M t Φ = Φ.timeSlice t :=
  (rfl)

variable (J n M) in
/-- The final diffeomorphism, as a homomorphism from the group of diffeotopies to the
self-diffeomorphism group. -/
def finalHom : Diffeotopy J n M →* M ≃ₘ^n⟮J, J⟯ M :=
  timeSliceHom J n M 1

@[simp]
theorem finalHom_apply (Φ : Diffeotopy J n M) : finalHom J n M Φ = Φ.final :=
  (final_def Φ).symm

/-- The final diffeomorphism of a product of diffeotopies is the product of the final
diffeomorphisms. -/
@[simp]
theorem final_mul (Φ Ψ : Diffeotopy J n M) : (Φ * Ψ).final = Φ.final * Ψ.final := by
  simp only [← finalHom_apply, map_mul]

/-- The final diffeomorphism of the unit diffeotopy is the identity. -/
@[simp]
theorem final_one : (1 : Diffeotopy J n M).final = 1 := by
  simp only [← finalHom_apply, map_one]

/-- The final diffeomorphism of the inverse diffeotopy is the inverse final diffeomorphism. -/
@[simp]
theorem final_inv (Φ : Diffeotopy J n M) : Φ⁻¹.final = Φ.final⁻¹ := by
  simp only [← finalHom_apply, map_inv]

/-! ### Diffeotopies through a subgroup -/

/-- The **diffeotopies through a subgroup** `S` of self-diffeomorphisms: those all of whose time
slices lie in `S`. For the stabilizer of a symplectic form `ω` these are the symplectic isotopies
starting at the identity. -/
def sliceSubgroup (S : Subgroup (M ≃ₘ^n⟮J, J⟯ M)) : Subgroup (Diffeotopy J n M) :=
  ⨅ t, S.comap (timeSliceHom J n M t)

/-- A diffeotopy lies in `sliceSubgroup S` exactly when every time slice lies in `S`. -/
theorem mem_sliceSubgroup {S : Subgroup (M ≃ₘ^n⟮J, J⟯ M)} {Φ : Diffeotopy J n M} :
    Φ ∈ sliceSubgroup S ↔ ∀ t, Φ.timeSlice t ∈ S := by
  simp [sliceSubgroup, Subgroup.mem_iInf]

/-- The final diffeomorphism of a diffeotopy through `S` lies in `S`. -/
theorem final_mem_of_mem_sliceSubgroup {S : Subgroup (M ≃ₘ^n⟮J, J⟯ M)} {Φ : Diffeotopy J n M}
    (hΦ : Φ ∈ sliceSubgroup S) : Φ.final ∈ S := by
  rw [final_def]
  exact mem_sliceSubgroup.1 hΦ 1

/-- Every diffeotopy runs through the whole self-diffeomorphism group. -/
@[simp]
theorem sliceSubgroup_top : sliceSubgroup (⊤ : Subgroup (M ≃ₘ^n⟮J, J⟯ M)) = ⊤ := by
  simp [sliceSubgroup]

/-- Diffeotopies through a smaller subgroup run through a larger one. -/
theorem sliceSubgroup_mono {S S' : Subgroup (M ≃ₘ^n⟮J, J⟯ M)} (h : S ≤ S') :
    sliceSubgroup S ≤ sliceSubgroup S' := fun _ hΦ ↦
  mem_sliceSubgroup.2 fun t ↦ h (mem_sliceSubgroup.1 hΦ t)

end Diffeotopy

end TauCeti
