/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Further results on exterior powers

This file records that the `d`th exterior power of a finite free module over a commutative ring
vanishes as soon as `d` exceeds the rank of the module.

It then builds the surjection `exteriorPower.fromTensorPower : ⨂[R]^n M →ₗ[R] ⋀[R]^n M` that is
left inverse, up to the factor `n!`, to Mathlib's antisymmetrization
`exteriorPower.toTensorPower`: composing the antisymmetrization with it is `n! • id` on the exterior
power, while composing the two the other way round is the antisymmetrization operator
`∑_σ sgn(σ) σ` on the tensor power. Consequently the antisymmetrization is injective once `n!` is a
unit in the base ring, and its image is the image of that operator. That is the statement a Young
symmetrizer of a one-column shape consumes.

Finally, it describes images of exterior powers under induced maps: inside the exterior algebra,
the image of `⋀ⁿ M` under `f` is the `n`th power of the degree-one image of `f`, and over a field an
injective map embeds `⋀ⁿ V` with its binomial dimension.

## Main definitions

* `exteriorPower.fromTensorPower` is the canonical surjection of the tensor power onto the
  exterior power.
## Main results

* `exteriorPower.eq_zero_of_finrank_lt` states that every element of `⋀[R]^d M` is zero when
  `Module.finrank R M < d`.
* `exteriorPower.fromTensorPower_comp_toTensorPower`: antisymmetrizing and projecting back is
  multiplication by `n!`, whence `exteriorPower.toTensorPower_injective`.
* `exteriorPower.ιMulti_ne_zero_iff`: over a field, an exterior product of vectors is nonzero
  exactly when the vectors are linearly independent.
* `exteriorPower.toTensorPower_injective_of_free`: antisymmetrization is injective for free
  modules in every characteristic, without factorial invertibility.
* `exteriorPower.range_toTensorPower`: the image of the antisymmetrization is the image of the
  antisymmetrization operator on the tensor power.
* `exteriorPower.toTensorPower_comp_map` and `exteriorPower.map_comp_fromTensorPower`: the
  antisymmetrization and the canonical surjection are natural in the module.
* `TauCeti.ExteriorAlgebra.exteriorPower_map_map`: the image of `⋀ⁿ M` in the exterior algebra
  under the map induced by `f` is the `n`th power of the degree-one image of `f`.
* `TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one` and
  `TauCeti.ExteriorAlgebra.ι_ιInv_of_mem_exteriorPower_one`: the first exterior power consists of
  the vectors, and `ExteriorAlgebra.ιInv` recovers the vector from its image.
* `TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower` and `TauCeti.ExteriorAlgebra.wedgeLeft`:
  left multiplication by a vector carries `⋀ⁿ M` into `⋀ⁿ⁺¹ M`, packaged as the linear map
  `v ↦ m ∧ v` with values in degree `n + 1`.
* `TauCeti.exteriorPower.finrank_range_map`: over a field, the image of `⋀ⁿ V` under the map
  induced by an injective linear map has dimension `(dim V).choose n`.
* `TauCeti.exteriorPower.mem_span_range_iff_ι_mul_ιMulti_eq_zero`: over a field, a vector lies in
  the span of a linearly independent family exactly when its product with the exterior product of
  the family vanishes.

## References

The results use Mathlib's exterior-power basis and dimension formula from
`Mathlib.LinearAlgebra.ExteriorPower.Basis`, by Sophie Morel and Daniel Morrison.
-/

public section

open scoped BigOperators TensorProduct

universe u w

variable {R : Type u} {M : Type w}

namespace exteriorPower

section Vanishing

variable [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

/-- An exterior power above the rank of a finite free module is zero. -/
theorem eq_zero_of_finrank_lt (d : ℕ) (h : Module.finrank R M < d) (x : ⋀[R]^d M) :
    x = 0 := by
  have : Subsingleton (⋀[R]^d M) := by
    rcases subsingleton_or_nontrivial R with _ | _
    · exact Module.subsingleton R _
    · rw [← Module.finrank_eq_zero_iff_of_free R, finrank_eq, Nat.choose_eq_zero_iff]
      exact h
  exact Subsingleton.elim x 0

end Vanishing

/-! ### Antisymmetrization of free modules -/

section Free

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Pairing with a pure exterior product of linear forms factors through the
antisymmetrization into the tensor power. -/
theorem pairingDual_ιMulti_apply {n : ℕ} (g : Fin n → Module.Dual R M) (x : ⋀[R]^n M) :
    pairingDual R M n (ιMulti R n g) x =
      TensorPower.multilinearMapToDual R M n g (toTensorPower R M n x) := by
  simp [pairingDual, alternatingMapToDual]

/-- Antisymmetrization embeds every exterior power of a free module into its tensor power,
over any commutative ring, without requiring the factorial to be invertible. -/
theorem toTensorPower_injective_of_free [Module.Free R M] {n : ℕ} :
    Function.Injective (toTensorPower R M n) := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex R M) := linearOrderOfSTO WellOrderingRel
  let b := Module.Free.chooseBasis R M
  -- Each exterior-basis coordinate factors through antisymmetrization.
  intro x y h
  apply (b.exteriorPower n).repr.injective
  ext s
  rw [basis_repr_apply, basis_repr_apply]
  simp only [ιMultiDual, ιMulti_family, pairingDual_ιMulti_apply, h]

end Free

/-! ### The exterior power as a quotient of the tensor power -/

section FromTensorPower

variable [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ)

variable (R M) in
/-- **The canonical surjection of the tensor power onto the exterior power**, sending a pure
tensor to the corresponding exterior product.

Mathlib's `exteriorPower.toTensorPower` runs the other way, by antisymmetrization; antisymmetrizing
and then projecting back is `n!` on the exterior power, while projecting and then antisymmetrizing
is the antisymmetrization operator `∑_σ sgn(σ) σ` on the tensor power. -/
noncomputable def fromTensorPower : (⨂[R]^n M) →ₗ[R] ⋀[R]^n M :=
  PiTensorProduct.lift (ιMulti R n).toMultilinearMap

@[simp]
theorem fromTensorPower_tprod (m : Fin n → M) :
    fromTensorPower R M n (PiTensorProduct.tprod R m) = ιMulti R n m :=
  PiTensorProduct.lift.tprod m

theorem fromTensorPower_surjective : Function.Surjective (fromTensorPower R M n) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← ιMulti_span R n M, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  exact ⟨PiTensorProduct.tprod R v, fromTensorPower_tprod n v⟩

/-- Antisymmetrizing an exterior product and projecting it back multiplies by `n!`: each of the
`n!` signed reorderings returns the same exterior product. -/
@[simp]
theorem fromTensorPower_comp_toTensorPower :
    (fromTensorPower R M n) ∘ₗ (toTensorPower R M n) =
      n.factorial • LinearMap.id (R := R) (M := ⋀[R]^n M) := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  have hsq : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ)) * ((Equiv.Perm.sign σ : ℤ)) = 1 := fun σ => by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have h : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ)) • ιMulti R n (fun i => v (σ i)) = ιMulti R n v := fun σ => by
    rw [← Function.comp_def v σ, (ιMulti R n).map_perm, Units.smul_def, smul_smul, hsq, one_smul]
  rw [LinearMap.coe_comp, Function.comp_apply, toTensorPower_apply_ιMulti, map_sum]
  simp only [Units.smul_def, map_zsmul, fromTensorPower_tprod, h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    LinearMap.smul_apply, LinearMap.id_apply]

/-- The antisymmetrization is injective as soon as `n!` is a unit in the base ring, for instance
over a `ℚ`-algebra. -/
theorem toTensorPower_injective (h : IsUnit (n.factorial : R)) :
    Function.Injective (toTensorPower R M n) := by
  obtain ⟨u, hu⟩ := h
  -- Rescaling the canonical surjection by `u⁻¹` makes it a left inverse of the antisymmetrization.
  refine LinearMap.injective_of_comp_eq_id _ (((u⁻¹ : Rˣ) : R) • fromTensorPower R M n) ?_
  rw [LinearMap.smul_comp, fromTensorPower_comp_toTensorPower, ← Nat.cast_smul_eq_nsmul R,
    smul_smul, ← hu, u.inv_mul, one_smul]

/-- Projecting a tensor to the exterior power and antisymmetrizing it back is the
antisymmetrization operator `∑_σ sgn(σ) σ` of the tensor power. -/
theorem toTensorPower_comp_fromTensorPower :
    (toTensorPower R M n) ∘ₗ (fromTensorPower R M n) =
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
        (PiTensorProduct.reindex R (fun _ : Fin n => M) σ).toLinearMap := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    LinearMap.coe_comp, Function.comp_apply, fromTensorPower_tprod,
    toTensorPower_apply_ιMulti, LinearMap.sum_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
  simp [Units.smul_def, Equiv.Perm.inv_def]

/-- The antisymmetrization is natural in the module. -/
theorem toTensorPower_comp_map {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (toTensorPower R N n) ∘ₗ (map n f) =
      (PiTensorProduct.map fun _ : Fin n => f) ∘ₗ (toTensorPower R M n) := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  simp [Units.smul_def, Function.comp_def]

/-- The canonical surjection is natural in the module. -/
theorem map_comp_fromTensorPower {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (map n f) ∘ₗ (fromTensorPower R M n) =
      (fromTensorPower R N n) ∘ₗ (PiTensorProduct.map fun _ : Fin n => f) := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
  simp [Function.comp_def]

/-- The image of the antisymmetrization is the image of the antisymmetrization operator
`∑_σ sgn(σ) σ` on the tensor power. -/
theorem range_toTensorPower :
    LinearMap.range (toTensorPower R M n) =
      LinearMap.range (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
        (PiTensorProduct.reindex R (fun _ : Fin n => M) σ).toLinearMap) := by
  rw [← toTensorPower_comp_fromTensorPower, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (fromTensorPower_surjective n), Submodule.map_top]

end FromTensorPower

/-! ### Exterior products over a field -/

section Field

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- Over a field, the exterior product of `n` vectors is nonzero exactly when they are linearly
independent. -/
theorem ιMulti_ne_zero_iff {n : ℕ} (v : Fin n → V) :
    ιMulti K n v ≠ 0 ↔ LinearIndependent K v := by
  refine ⟨fun h ↦ by_contra fun hv ↦ h ((ιMulti K n).map_linearDependent v hv), fun hv ↦ ?_⟩
  -- The only `n`-element subset of `Fin n` is enumerated by the identity.
  have hs : (Finset.univ : Finset (Fin n)).card = n := by simp
  have he : ⇑(Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hs)) = id := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact (Finset.orderEmbOfFin_unique hs (fun _ ↦ Finset.mem_univ _) strictMono_id).symm
  simpa [ιMulti_family, he] using (ιMulti_family_linearIndependent_field (n := n) hv).ne_zero
    (Set.powersetCard.ofCard hs)

end Field

end exteriorPower

namespace TauCeti

namespace ExteriorAlgebra

variable [CommRing R] [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]

/-- Inside the exterior algebra, the image of the `n`th exterior power under the map induced by
`f` is the `n`th power of the degree-one image of the range of `f`. -/
theorem exteriorPower_map_map (n : ℕ) (f : M →ₗ[R] N) :
    (⋀[R]^n M).map (_root_.ExteriorAlgebra.map f).toLinearMap =
      ((LinearMap.range f).map (_root_.ExteriorAlgebra.ι R)) ^ n := by
  rw [_root_.ExteriorAlgebra.exteriorPower, Submodule.map_pow,
    _root_.ExteriorAlgebra.ι_range_map_map]

/-- A vector lies in the first exterior power. -/
theorem ι_mem_exteriorPower_one (m : M) : _root_.ExteriorAlgebra.ι R m ∈ ⋀[R]^1 M := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_one]
  exact LinearMap.mem_range_self _ m

/-- An element of the first exterior power is the vector `ExteriorAlgebra.ιInv` reads off from
it. -/
theorem ι_ιInv_of_mem_exteriorPower_one {x : _root_.ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^1 M) :
    _root_.ExteriorAlgebra.ι R (_root_.ExteriorAlgebra.ιInv x) = x := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_one] at hx
  obtain ⟨m, rfl⟩ := hx
  rw [_root_.ExteriorAlgebra.ι_leftInverse]

/-- Left multiplication by a vector raises the exterior degree by one: it carries the `n`-th
exterior power into the `(n + 1)`-th. -/
theorem ι_mul_mem_exteriorPower (m : M) {n : ℕ} {x : _root_.ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) :
    _root_.ExteriorAlgebra.ι R m * x ∈ ⋀[R]^(n + 1) M := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ m) hx

/-- Exterior multiplication `v ↦ m ∧ v` by a vector `m`, from the `n`-th exterior power to the
`(n + 1)`-th. Mathlib's `exteriorPower.wedge R M 1 n` is the same product with values in degree
`1 + n`, which is not definitionally `n + 1`; this form composes with maps out of `⋀ⁿ⁺¹ M`. -/
def wedgeLeft (m : M) (n : ℕ) : ⋀[R]^n M →ₗ[R] ⋀[R]^(n + 1) M :=
  (LinearMap.mulLeft R (_root_.ExteriorAlgebra.ι R m)).restrict fun _ hx ↦
    ι_mul_mem_exteriorPower m hx

/-- `wedgeLeft m n` is left multiplication by `ι R m` in the exterior algebra. -/
@[simp]
theorem coe_wedgeLeft_apply (m : M) (n : ℕ) (x : ⋀[R]^n M) :
    (wedgeLeft m n x : _root_.ExteriorAlgebra R M) = _root_.ExteriorAlgebra.ι R m * x :=
  (rfl)

/-- `wedgeLeft m n` prepends `m` to a wedge product of vectors: `m ∧ (v₀ ∧ ⋯ ∧ vₙ₋₁)`. -/
@[simp]
theorem wedgeLeft_ιMulti (m : M) (n : ℕ) (v : Fin n → M) :
    wedgeLeft m n (exteriorPower.ιMulti R n v) = exteriorPower.ιMulti R (n + 1) (Fin.cons m v) := by
  ext
  simp [_root_.ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]

end ExteriorAlgebra

namespace exteriorPower

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup W] [Module K W]

/-- Over a field, the image of the `n`th exterior power of a finite-dimensional space under the
map induced by an injective linear map has dimension `(dim V).choose n`. -/
theorem finrank_range_map {f : V →ₗ[K] W} (hf : Function.Injective f) (n : ℕ) :
    Module.finrank K (LinearMap.range (_root_.exteriorPower.map n f)) =
      (Module.finrank K V).choose n := by
  rw [LinearMap.finrank_range_of_inj (_root_.exteriorPower.map_injective_field hf),
    _root_.exteriorPower.finrank_eq]

omit [Module.Finite K V] in
/-- Over a field, a vector lies in the span of a linearly independent family of `n` vectors exactly
when its product with the exterior product of the family vanishes in the exterior algebra. -/
theorem mem_span_range_iff_ι_mul_ιMulti_eq_zero {n : ℕ} {v : Fin n → V}
    (hv : LinearIndependent K v) (w : V) :
    w ∈ Submodule.span K (Set.range v) ↔
      _root_.ExteriorAlgebra.ι K w * (_root_.exteriorPower.ιMulti K n v : ExteriorAlgebra K V) =
        0 := by
  have hcons : w ∈ Submodule.span K (Set.range v) ↔
      ¬LinearIndependent K (Fin.cons w v : Fin (n + 1) → V) := by
    rw [linearIndependent_finCons]
    tauto
  rw [hcons, ← _root_.exteriorPower.ιMulti_ne_zero_iff, not_not, ← ZeroMemClass.coe_eq_zero,
    _root_.exteriorPower.ιMulti_apply_coe, _root_.ExteriorAlgebra.ιMulti_succ_apply,
    _root_.exteriorPower.ιMulti_apply_coe]
  simp [Matrix.vecTail, Function.comp_def]

end exteriorPower

end TauCeti
