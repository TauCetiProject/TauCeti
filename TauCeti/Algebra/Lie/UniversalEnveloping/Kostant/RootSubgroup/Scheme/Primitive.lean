/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.Algebra.Module.Primitive.Basic
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Triangular
import TauCeti.LinearAlgebra.SymmetricAlgebra.Basic
import TauCeti.LinearAlgebra.Basis.Basic

/-!
# Closed root subgroups detected by primitive images

Let a nilpotent root operator `op` preserve an integral lattice through all its divided powers. This
module provides two integral closed-immersion criteria for the induced root morphism `𝔾ₐ ⟶ GLₙ`
over `ℤ`:

* **Two-step string criterion** (for any integral lattice basis): if a lattice vector `m` satisfies
  `op (op m) = 0` and `op m` is primitive in the lattice, then the root coordinate map is
  surjective and the root morphism is a closed immersion. This subsumes the basis-step criterion in
  `TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion`.
* **Cartan weight-basis criterion** (without `op (op m) = 0`): in a Cartan weight basis for a
  nonzero integral root `α`, the existence of any lattice vector `m` with `op m` primitive already
  makes the root coordinate map surjective and the root morphism a closed immersion. This covers
  higher-length root strings such as the adjoint representation of `PSL₂`, where no primitive image
  vector lies in `op(ker op²)`.

## Main results

* `kostantRootSubgroupCoordinateMap_surjective_of_isPrimitive` and
  `isClosedImmersion_kostantRootSubgroup_of_isPrimitive`: coordinate surjectivity and closed
  immersion from a primitive two-step string in any lattice basis.
* `kostantRootSubgroupCoordinateMap_genericMatrix_of_weight_eq`: pullback of single-root-shift
  generic matrix entries in a Cartan weight basis.
* `kostantRootSubgroupCoordinateMap_surjective_of_isPrimitive_of_isCartanWeightVector` and
  `isClosedImmersion_kostantRootSubgroup_of_isPrimitive_of_isCartanWeightVector`: coordinate
  surjectivity and closed immersion from a primitive image vector in a Cartan weight basis.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L ι κ : Type*} {V : Type}
variable [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V]
variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V) (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (i : ι) (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)

local notation "op" => kostantRootOperator e h ρ M hM i

/-- On a two-step string, the universal root matrix sends `m` to `m + X • e m`,
read in the chosen lattice basis. The vector need not be a basis vector. -/
theorem map_genericMatrix_kostantRootSubgroupCoordinateMap_mulVec_repr_of_sq_eq_zero (m : M)
    (hsq : op (op m) = 0) :
    ((GeneralLinear.genericMatrix ℤ n).map
        (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom.toAlgHom).mulVec
        (fun s => (b.repr m s : AdditiveGroup.coordinateHopfAlgebra ℤ)) =
      fun r => (b.repr m r : AdditiveGroup.coordinateHopfAlgebra ℤ) +
        SymmetricAlgebra.ι ℤ ℤ 1 * (b.repr (op m) r : AdditiveGroup.coordinateHopfAlgebra ℤ) := by
  classical
  let A : Type := AdditiveGroup.coordinateHopfAlgebra ℤ
  let : Algebra ℤ A := Ring.toIntAlgebra A
  let p := toConv (SymmetricAlgebra.lift
    (LinearMap.toSpanSingleton ℤ A (SymmetricAlgebra.ι ℤ ℤ 1)))
  have hsq' : (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) ^ 2 • (m : V) = 0 := by
    have hm := congrArg Subtype.val hsq
    simpa only [coe_kostantRootOperator_apply, ZeroMemClass.coe_zero, pow_two,
      Module.End.smul_def, mul_apply_eq_comp] using hm
  have haction : (kostantRootSubgroupPoints e h ρ M hM i hnil p).val (1 ⊗ₜ[ℤ] m) =
      1 ⊗ₜ[ℤ] m + (SymmetricAlgebra.ι ℤ ℤ 1) ⊗ₜ[ℤ] op m := by
    rw [kostantRootSubgroupPoints_val,
      baseChangeExp_tmul_of_pow_smul_eq_zero _ _ _ hnil _ _ _ hsq']
    have hfirst : integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M 1
        (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i 1 hv) m =
        op m := by
      apply Subtype.ext
      rw [coe_integralDividedPower_one_apply, coe_kostantRootOperator_apply,
        Module.End.smul_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      mul_one, integralDividedPower_zero, one_apply_eq_self, hfirst,
      AdditiveGroup.toAdd_gaPointsMulEquiv, p, SymmetricAlgebra.lift_ι_apply,
      LinearMap.toSpanSingleton_apply, one_smul]
  rw [map_genericMatrix_eq_kostantRootSubgroupMatrix]
  rw [coe_kostantRootSubgroupMatrix e h ρ M hM i hnil b p]
  have hrepr : (fun s => (b.repr m s : A)) = ⇑((b.baseChange A).repr (1 ⊗ₜ[ℤ] m)) := by
    ext s
    simp only [Module.Basis.baseChange_repr_tmul, zsmul_eq_mul, mul_one]
  rw [hrepr, LinearMap.toMatrix_mulVec_repr, haction]
  ext r
  simp only [map_add, Finsupp.add_apply, Module.Basis.baseChange_repr_tmul,
    zsmul_eq_mul, mul_comm, one_mul]

/-- A primitive two-step string makes the root-subgroup coordinate map surjective.
An integral functional taking value one on `e m` detects the polynomial generator. -/
theorem kostantRootSubgroupCoordinateMap_surjective_of_isPrimitive (m : M)
    (hsq : op (op m) = 0) (hprim : IsPrimitive (op m)) :
    Function.Surjective (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom := by
  classical
  obtain ⟨ℓ, hℓ⟩ := isPrimitive_def.mp hprim
  let C := GeneralLinear.coordinateHopfAlgebra ℤ n
  let f := (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom.toAlgHom
  let z : C := ∑ r, ℓ (b r) • ∑ s, b.repr m s • GeneralLinear.genericMatrix ℤ n r s
  have hz : f z = (ℓ m : AdditiveGroup.coordinateHopfAlgebra ℤ) +
      SymmetricAlgebra.ι ℤ ℤ 1 := by
    have hvec := map_genericMatrix_kostantRootSubgroupCoordinateMap_mulVec_repr_of_sq_eq_zero
      e h ρ M hM i hnil b m hsq
    simp only [z, map_sum, map_zsmul]
    have hrow (r : Fin n) : ∑ s,
        (b.repr m s : AdditiveGroup.coordinateHopfAlgebra ℤ) *
          f (GeneralLinear.genericMatrix ℤ n r s) =
        (b.repr m r : AdditiveGroup.coordinateHopfAlgebra ℤ) +
          SymmetricAlgebra.ι ℤ ℤ 1 * b.repr (op m) r := by
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, f, zsmul_eq_mul, mul_comm]
        using congrFun hvec r
    simp only [zsmul_eq_mul, hrow, mul_add]
    rw [Finset.sum_add_distrib]
    have heval (v : M) : ∑ r, (ℓ (b r) : AdditiveGroup.coordinateHopfAlgebra ℤ) *
        b.repr v r = (ℓ v : AdditiveGroup.coordinateHopfAlgebra ℤ) := by
      simpa [zsmul_eq_mul, mul_comm] using congrArg
        (Int.cast : ℤ → AdditiveGroup.coordinateHopfAlgebra ℤ)
        (b.apply_eq_sum_repr_zsmul ℓ v).symm
    rw [heval]
    congr 1
    calc
      _ = SymmetricAlgebra.ι ℤ ℤ 1 * ∑ r,
          (ℓ (b r) : AdditiveGroup.coordinateHopfAlgebra ℤ) * b.repr (op m) r := by
        rw [Finset.mul_sum]
        congr 1
        funext r
        ring
      _ = _ := by rw [heval, hℓ]; simp
  apply f.surjective_of_ι_one_mem_range
  refine ⟨z - algebraMap ℤ C (ℓ m), ?_⟩
  simp [map_sub, hz]

/-- The root morphism is a closed immersion whenever a primitive two-step lattice string
detects its parameter. This does not require adapting the lattice basis to the string. -/
theorem isClosedImmersion_kostantRootSubgroup_of_isPrimitive (m : M)
    (hsq : op (op m) = 0) (hprim : IsPrimitive (op m)) :
    IsClosedImmersion (kostantRootSubgroup e h ρ M hM i hnil b).hom.hom.left := by
  rw [kostantRootSubgroup_def]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
    (AdditiveGroup.groupScheme_def ℤ) (GeneralLinear.groupScheme_def ℤ n) _).2
    (kostantRootSubgroupCoordinateMap_surjective_of_isPrimitive e h ρ M hM i hnil b m hsq hprim)

/-- In a Cartan weight basis for a nonzero integral root `α`, every generic matrix entry
connecting weight `μ` to weight `μ + α` pulls back along the root coordinate map to a linear
multiple of the additive generator, with no constant or higher-degree divided-power terms. -/
theorem kostantRootSubgroupCoordinateMap_genericMatrix_of_weight_eq
    {wt : Fin n → κ → ℤ} (hwt : ∀ j, IsCartanWeightVector h ρ (wt j) ((b j : M) : V))
    {α : κ → ℤ} (hα : ∀ c, ⁅h c, e i⁆ = (α c : ℚ) • e i) (hα0 : α ≠ 0)
    {r s : Fin n} (hrs : wt r = wt s + α) :
    (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom.toAlgHom
        (GeneralLinear.genericMatrix ℤ n r s) =
      b.repr (op (b s)) r • SymmetricAlgebra.ι ℤ ℤ 1 := by
  let N := nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
  let D : ℕ → Matrix (Fin n) (Fin n) ℤ := fun k => LinearMap.toMatrix b b
    (integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M k
      (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i k hv))
  have hmat := congrArg (fun M => M r s)
    (map_genericMatrix_eq_kostantRootSubgroupMatrix e h ρ M hM i hnil b)
  simp only [Matrix.map_apply] at hmat
  rw [hmat, kostantRootSubgroupMatrix_eq_sum e h ρ M hM i hnil b (N + 2) D (by omega)
    (fun k _ s' => by simp [D, LinearMap.toMatrix_apply])]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
    AdditiveGroup.toAdd_gaPointsMulEquiv, SymmetricAlgebra.lift_ι_apply,
    LinearMap.toSpanSingleton_apply, one_smul]
  rw [Finset.sum_eq_single 1]
  · simp only [D, LinearMap.toMatrix_apply, pow_one]
    rw [← kostantRootOperator_def, smul_eq_mul, zsmul_eq_mul, mul_comm]
  · intro k _ hk1
    have hne : wt r ≠ wt s + k • α := by
      intro heq
      have heq' : (1 : ℕ) • α = k • α := by
        simpa only [one_nsmul] using add_left_cancel (hrs.symm.trans heq)
      exact hk1 (IsAddTorsionFree.nsmul_left_injective hα0 heq').symm
    have hzero : D k r s = 0 := by
      simp only [D, LinearMap.toMatrix_apply]
      exact repr_integralDividedPower_eq_zero_of_weight_ne e h ρ M hM b wt hwt hα hne
    simp [hzero]
  · intro hmem
    exact False.elim (hmem (Finset.mem_range.mpr (by omega)))

/-- In a Cartan weight basis for a nonzero integral root `α`, any lattice vector `m` whose image
`op m` is primitive makes the root-subgroup coordinate map surjective, without requiring
`op (op m) = 0`. -/
theorem kostantRootSubgroupCoordinateMap_surjective_of_isPrimitive_of_isCartanWeightVector
    {wt : Fin n → κ → ℤ} (hwt : ∀ j, IsCartanWeightVector h ρ (wt j) ((b j : M) : V))
    {α : κ → ℤ} (hα : ∀ c, ⁅h c, e i⁆ = (α c : ℚ) • e i) (hα0 : α ≠ 0)
    (m : M) (hprim : IsPrimitive (op m)) :
    Function.Surjective (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom := by
  classical
  obtain ⟨ℓ, hℓ⟩ := isPrimitive_def.mp hprim
  let C := GeneralLinear.coordinateHopfAlgebra ℤ n
  let f := (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom.toAlgHom
  let z : C := ∑ s, ∑ r with wt r = wt s + α,
    (ℓ (b r) * b.repr m s) • GeneralLinear.genericMatrix ℤ n r s
  have hop_zero {r s : Fin n} (hrs : wt r ≠ wt s + α) : b.repr (op (b s)) r = 0 := by
    rw [kostantRootOperator_def]
    exact repr_integralDividedPower_eq_zero_of_weight_ne e h ρ M hM b wt hwt hα
      (by simpa only [one_nsmul] using hrs)
  have hinner (s : Fin n) :
      (∑ r with wt r = wt s + α, (ℓ (b r) * b.repr m s) * b.repr (op (b s)) r) =
        b.repr m s * ℓ (op (b s)) := by
    rw [Finset.sum_subset (Finset.filter_subset _ Finset.univ)]
    · calc
        (∑ r, (ℓ (b r) * b.repr m s) * b.repr (op (b s)) r) =
            b.repr m s * ∑ r, b.repr (op (b s)) r • ℓ (b r) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [smul_eq_mul]
          ring
        _ = b.repr m s * ℓ (op (b s)) := by rw [← b.apply_eq_sum_repr_zsmul]
    · intro r _ hr
      rw [Finset.mem_filter] at hr
      rw [hop_zero (not_and.mp hr (Finset.mem_univ r)), mul_zero]
  have hsum_one :
      (∑ s, ∑ r with wt r = wt s + α, (ℓ (b r) * b.repr m s) * b.repr (op (b s)) r) = 1 := by
    calc
      _ = ∑ s, b.repr m s • ℓ (op (b s)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hinner s]
        rfl
      _ = ℓ (op (∑ s, b.repr m s • b s)) := by simp only [map_sum, map_zsmul]
      _ = 1 := by rw [b.sum_repr m, hℓ]
  apply f.surjective_of_ι_one_mem_range
  refine ⟨z, ?_⟩
  calc
    f z = ∑ s, ∑ r with wt r = wt s + α,
        ((ℓ (b r) * b.repr m s) * b.repr (op (b s)) r) • SymmetricAlgebra.ι ℤ ℤ 1 := by
      simp only [z, map_sum, map_zsmul]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r hr => ?_
      rw [kostantRootSubgroupCoordinateMap_genericMatrix_of_weight_eq e h ρ M hM i hnil b
        hwt hα hα0 (Finset.mem_filter.mp hr).2, smul_smul]
    _ = (∑ s, ∑ r with wt r = wt s + α,
          (ℓ (b r) * b.repr m s) * b.repr (op (b s)) r) • SymmetricAlgebra.ι ℤ ℤ 1 := by
      simp_rw [← Finset.sum_smul]
    _ = SymmetricAlgebra.ι ℤ ℤ 1 := by rw [hsum_one, one_smul]

/-- In a Cartan weight basis for a nonzero integral root `α`, the root morphism is a closed
immersion whenever `op` has a primitive vector in its image. -/
theorem isClosedImmersion_kostantRootSubgroup_of_isPrimitive_of_isCartanWeightVector
    {wt : Fin n → κ → ℤ} (hwt : ∀ j, IsCartanWeightVector h ρ (wt j) ((b j : M) : V))
    {α : κ → ℤ} (hα : ∀ c, ⁅h c, e i⁆ = (α c : ℚ) • e i) (hα0 : α ≠ 0)
    (m : M) (hprim : IsPrimitive (op m)) :
    IsClosedImmersion (kostantRootSubgroup e h ρ M hM i hnil b).hom.hom.left := by
  rw [kostantRootSubgroup_def]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
    (AdditiveGroup.groupScheme_def ℤ) (GeneralLinear.groupScheme_def ℤ n) _).2
    (kostantRootSubgroupCoordinateMap_surjective_of_isPrimitive_of_isCartanWeightVector
      e h ρ M hM i hnil b hwt hα hα0 m hprim)

end TauCeti.UniversalEnvelopingAlgebra
