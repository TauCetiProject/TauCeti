/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Generated

/-!
# The torus of the Suzuki group

The standard generators of `TauCeti.suzukiGroup m` are the lower unitriangular matrices `u(a, b)`
and the antidiagonal Weyl element `w`. This file adds the diagonal torus

```text
h(κ) = diag (κ, κ^θ / κ, κ / κ^θ, κ⁻¹),      θ = 2^(m+1),
```

as a homomorphism `TauCeti.Suzuki.torus` from the multiplicative group of the generator field,
computes its conjugation action on the unipotent generators, and proves that its image lies in
the generated group. The torus is not a generator, so its membership is a computation: the
rank-one Bruhat relation

```text
w u(0, b) w = u(b^(1-θ), b⁻¹) · h(b^θ) · w · u(b^(1-θ), 0)      (b ≠ 0)
```

exhibits `h(b^θ) w` as a product of generators, and since `x ↦ x^θ` is a bijection of the finite
generator field every torus element is some `h(b^θ)`. The Bruhat decomposition of the Suzuki group
with respect to the point at infinity, and the identification of the group with the Steinberg
fixed points, consume the torus in `TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Generation`.

## Main definitions

* `TauCeti.Suzuki.torusMatrix`: the diagonal torus matrix `h(κ)`.
* `TauCeti.Suzuki.torus`: the torus as a homomorphism `𝔽_q^× →* GL₄(𝔽_q)`.
* `TauCeti.Suzuki.borelSubgroup`: the Borel subgroup `B = H U`, the join of the range of the torus
  and the unipotent subgroup, and `TauCeti.Suzuki.borelSubgroupOf`, the same subgroup inside the
  Suzuki group.

## Main results

* `TauCeti.Suzuki.torus_mul_unipotent_mul_torus_inv`: the torus normalizes the unipotent
  generators, `h(κ) u(a, b) h(κ)⁻¹ = u(κ^θ κ⁻² a, κ^(-θ) b)`.
* `TauCeti.Suzuki.commutatorElement_torus_unipotent`: the commutator of a torus element with a
  unipotent generator, read off the conjugation formula.
* `TauCeti.Suzuki.weyl_mul_unipotent_zero_mul_weyl`: the rank-one Bruhat relation.
* `TauCeti.Suzuki.torus_mem_suzukiGroup`: every torus element is a product of the standard
  generators.
* `TauCeti.Suzuki.mem_borelSubgroup`: the Borel subgroup consists of the products `h(κ) u(a, b)`.
* `TauCeti.Suzuki.weyl_mul_unipotent_mul_weyl_mem_borelSubgroup_iff`: the Weyl element
  conjugates `u(a, b)` into the Borel subgroup only when `u(a, b) = 1`.
* `TauCeti.Suzuki.normalClosure_unipotentSubgroupOf`: the conjugates of the unipotent subgroup
  generate the Suzuki group.

## References

* M. Suzuki, *On a class of doubly transitive groups*, Annals of Mathematics **75** (1962),
  105--145.
* R. A. Wilson, *The Finite Simple Groups*, Springer GTM 251 (2009), §4.2.
-/

public section

noncomputable section

open Matrix
open scoped commutatorElement

namespace TauCeti

namespace Suzuki

variable (m : ℕ)

/-! ## The torus -/

/-- The torus matrix of the Suzuki group at the parameter `κ`, `diag (κ, κ^θ / κ, κ / κ^θ, κ⁻¹)`
with `θ = 2^(m+1)`. Writing `κ = λ^(2^m + 1)`, which is possible since `2^m + 1` is prime to
`2^(2m+1) - 1`, this is the usual diagonal matrix `diag (λ^(2^m+1), λ^(2^m), λ^(-2^m), λ^(-2^m-1))`
of the literature. -/
def torusMatrix (κ : (GaloisField 2 (2 * m + 1))ˣ) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1)) :=
  Matrix.diagonal ![κ, κ ^ 2 ^ (m + 1) * κ⁻¹, κ * (κ ^ 2 ^ (m + 1))⁻¹, κ⁻¹]

/-- An entry of the torus matrix. -/
@[simp]
theorem torusMatrix_apply (κ : (GaloisField 2 (2 * m + 1))ˣ) (i j : Fin 4) :
    torusMatrix m κ i j =
      Matrix.diagonal ![(κ : GaloisField 2 (2 * m + 1)),
        (κ : GaloisField 2 (2 * m + 1)) ^ 2 ^ (m + 1) * (κ : GaloisField 2 (2 * m + 1))⁻¹,
        (κ : GaloisField 2 (2 * m + 1)) * ((κ : GaloisField 2 (2 * m + 1)) ^ 2 ^ (m + 1))⁻¹,
        (κ : GaloisField 2 (2 * m + 1))⁻¹] i j := by
  simp [torusMatrix]

/-- The torus matrix has determinant one. -/
@[simp]
theorem det_torusMatrix (κ : (GaloisField 2 (2 * m + 1))ˣ) : (torusMatrix m κ).det = 1 := by
  have hκ : (κ : GaloisField 2 (2 * m + 1)) ≠ 0 := κ.ne_zero
  rw [torusMatrix, det_diagonal, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val]
  field_simp

/-- The torus matrix at `1` is the identity. -/
@[simp]
theorem torusMatrix_one : torusMatrix m 1 = 1 := by
  rw [torusMatrix, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

/-- The torus matrices multiply through their parameters. -/
theorem torusMatrix_mul (κ μ : (GaloisField 2 (2 * m + 1))ˣ) :
    torusMatrix m (κ * μ) = torusMatrix m κ * torusMatrix m μ := by
  rw [torusMatrix, torusMatrix, torusMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_pow] <;> ring

/-- The torus of the Suzuki group: the homomorphism `κ ↦ h(κ)` from the multiplicative group
of the generator field into the general linear group, with `h(κ)` the matrix `torusMatrix m κ`. -/
def torus : (GaloisField 2 (2 * m + 1))ˣ →* GL (Fin 4) (GaloisField 2 (2 * m + 1)) where
  toFun κ := Matrix.GeneralLinearGroup.mk'' (torusMatrix m κ) (by simp)
  map_one' := Matrix.GeneralLinearGroup.ext fun i j ↦ by
    rw [Matrix.GeneralLinearGroup.val_mk'', torusMatrix_one]
    rfl
  map_mul' κ μ := Matrix.GeneralLinearGroup.ext fun i j ↦ by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.val_mk'', Matrix.GeneralLinearGroup.val_mk'',
      Matrix.GeneralLinearGroup.val_mk'', torusMatrix_mul]

/-- The underlying matrix of `torus m κ` is `torusMatrix m κ`. -/
@[simp]
theorem coe_torus (κ : (GaloisField 2 (2 * m + 1))ˣ) :
    (torus m κ : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) = torusMatrix m κ :=
  Matrix.GeneralLinearGroup.val_mk'' _ _

/-! ## The action of the torus on the unipotent generators -/

/-- **The torus normalizes the unipotent generators**:
`h(κ) u(a, b) h(κ)⁻¹ = u(κ^θ κ⁻² a, κ^(-θ) b)`, with `θ = 2^(m+1)`. -/
@[simp]
theorem torus_mul_unipotent_mul_torus_inv (κ : (GaloisField 2 (2 * m + 1))ˣ)
    (a b : GaloisField 2 (2 * m + 1)) :
    torus m κ * unipotent m a b * (torus m κ)⁻¹ =
      unipotent m
        ((κ : GaloisField 2 (2 * m + 1)) ^ 2 ^ (m + 1) / (κ : GaloisField 2 (2 * m + 1)) ^ 2 * a)
        (b / (κ : GaloisField 2 (2 * m + 1)) ^ 2 ^ (m + 1)) := by
  have hκ : (κ : GaloisField 2 (2 * m + 1)) ≠ 0 := κ.ne_zero
  rw [← map_inv]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, coe_unipotent, coe_torus]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, mul_pow, div_pow, inv_pow, torusMatrix_apply, Matrix.diagonal_apply]
  all_goals field_simp
  all_goals ring

/-- **The commutator of a torus element with a unipotent generator** is again a unipotent
generator: writing `λ = κ^θ κ⁻²` and `μ = κ^(-θ)`,
`[h(κ), u(a, b)] = u((λ + 1) a, (μ + 1) b + (λ + 1) a^(1+θ))`. -/
@[simp]
theorem commutatorElement_torus_unipotent (κ : (GaloisField 2 (2 * m + 1))ˣ)
    (a b : GaloisField 2 (2 * m + 1)) :
    ⁅torus m κ, unipotent m a b⁆ =
      unipotent m
        (((κ : GaloisField 2 (2 * m + 1)) ^ 2 ^ (m + 1) / (κ : GaloisField 2 (2 * m + 1)) ^ 2 + 1)
          * a)
        ((((κ : GaloisField 2 (2 * m + 1)) ^ 2 ^ (m + 1))⁻¹ + 1) * b +
          ((κ : GaloisField 2 (2 * m + 1)) ^ 2 ^ (m + 1) / (κ : GaloisField 2 (2 * m + 1)) ^ 2 + 1)
            * a * a ^ 2 ^ (m + 1)) := by
  rw [commutatorElement_def, torus_mul_unipotent_mul_torus_inv, unipotent_inv,
    unipotent_mul_unipotent]
  congr 1 <;> ring

/-! ## The rank-one Bruhat relation and the torus -/

/-- The rank-one Bruhat relation of the Suzuki group: conjugating the long-root generator
`u(0, b)` by the Weyl element lands in the big cell, `w u(0, b) w = u' h(b^θ) w u''` with
`u' = u(b^(1-θ), b⁻¹)` and `u'' = u(b^(1-θ), 0)`. -/
theorem weyl_mul_unipotent_zero_mul_weyl (b : GaloisField 2 (2 * m + 1)) (hb : b ≠ 0) :
    weyl m * unipotent m 0 b * weyl m =
      unipotent m (b / b ^ 2 ^ (m + 1)) b⁻¹ *
        torus m (Units.mk0 (b ^ 2 ^ (m + 1)) (pow_ne_zero _ hb)) * weyl m *
        unipotent m (b / b ^ 2 ^ (m + 1)) 0 := by
  have htwo : (2 : GaloisField 2 (2 * m + 1)) = 0 := CharTwo.two_eq_zero
  have hthree : (3 : GaloisField 2 (2 * m + 1)) = 1 := by linear_combination htwo
  have hfour : (4 : GaloisField 2 (2 * m + 1)) = 0 := by linear_combination 2 * htwo
  have hsix : (6 : GaloisField 2 (2 * m + 1)) = 0 := by linear_combination 3 * htwo
  have hB := pow_two_pow_succ_pow_two_pow_succ m b
  have hB0 : b ^ 2 ^ (m + 1) ≠ 0 := pow_ne_zero _ hb
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, coe_weyl, coe_unipotent, coe_torus]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, div_pow, inv_pow, hB]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp [htwo, hthree, hfour, hsix]

/-- Every torus element of the Suzuki group is a product of the standard generators: it is
read off the rank-one Bruhat relation at a `θ`-th root of its parameter. -/
theorem torus_mem_suzukiGroup (κ : (GaloisField 2 (2 * m + 1))ˣ) :
    torus m κ ∈ suzukiGroup m := by
  obtain ⟨b, hb⟩ :=
    (bijective_iterateFrobenius (GaloisField 2 (2 * m + 1)) 2 (m + 1)).2
      (κ : GaloisField 2 (2 * m + 1))
  rw [iterateFrobenius_def] at hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact κ.ne_zero (by simpa using hb.symm)
  have hκ : κ = Units.mk0 (b ^ 2 ^ (m + 1)) (pow_ne_zero _ hb0) := Units.ext (by simp [hb])
  have h := weyl_mul_unipotent_zero_mul_weyl m b hb0
  rw [← hκ] at h
  have ht : torus m κ =
      (unipotent m (b / b ^ 2 ^ (m + 1)) b⁻¹)⁻¹ * (weyl m * unipotent m 0 b * weyl m) *
        (unipotent m (b / b ^ 2 ^ (m + 1)) 0)⁻¹ * (weyl m)⁻¹ := by
    rw [h]
    group
  rw [ht]
  exact mul_mem (mul_mem (mul_mem (inv_mem (unipotent_mem_suzukiGroup _ _))
    (mul_mem (mul_mem weyl_mem_suzukiGroup (unipotent_mem_suzukiGroup _ _))
      weyl_mem_suzukiGroup)) (inv_mem (unipotent_mem_suzukiGroup _ _)))
    (inv_mem weyl_mem_suzukiGroup)

/-! ## The Borel subgroup -/

/-- The torus normalizes the unipotent subgroup. -/
theorem torus_mul_mul_inv_mem_unipotentSubgroup (κ : (GaloisField 2 (2 * m + 1))ˣ)
    {g : GL (Fin 4) (GaloisField 2 (2 * m + 1))} (hg : g ∈ unipotentSubgroup m) :
    torus m κ * g * (torus m κ)⁻¹ ∈ unipotentSubgroup m := by
  obtain ⟨a, b, rfl⟩ := mem_unipotentSubgroup.mp hg
  exact mem_unipotentSubgroup.mpr ⟨_, _, (torus_mul_unipotent_mul_torus_inv m κ a b).symm⟩

/-- The range of the torus normalizes the unipotent subgroup. -/
theorem range_torus_le_normalizer :
    (torus m).range ≤ Subgroup.normalizer (unipotentSubgroup m : Set _) := by
  rintro _ ⟨κ, rfl⟩
  refine Subgroup.mem_normalizer_iff.mpr fun g ↦
    ⟨torus_mul_mul_inv_mem_unipotentSubgroup m κ, fun hg ↦ ?_⟩
  simpa [map_inv, mul_assoc] using torus_mul_mul_inv_mem_unipotentSubgroup m κ⁻¹ hg

/-- The Borel subgroup `B = H U` of `GL₄(𝔽_(2^(2m+1)))`, the join of the range of the torus and
the unipotent subgroup. Since the torus normalizes the unipotent subgroup, it consists of the
products `h(κ) u(a, b)` (`TauCeti.Suzuki.mem_borelSubgroup`). -/
def borelSubgroup : Subgroup (GL (Fin 4) (GaloisField 2 (2 * m + 1))) :=
  (torus m).range ⊔ unipotentSubgroup m

variable {m} in
/-- The Borel subgroup consists of the products of a torus element and a standard unipotent
generator. -/
@[simp]
theorem mem_borelSubgroup {g : GL (Fin 4) (GaloisField 2 (2 * m + 1))} :
    g ∈ borelSubgroup m ↔ ∃ κ a b, torus m κ * unipotent m a b = g := by
  rw [← SetLike.mem_coe, borelSubgroup,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (range_torus_le_normalizer m)]
  simp [Set.mem_mul]

/-- The unipotent subgroup lies in the Borel subgroup. -/
theorem unipotentSubgroup_le_borelSubgroup : unipotentSubgroup m ≤ borelSubgroup m :=
  le_sup_right

/-- The Borel subgroup lies in the Suzuki group. -/
theorem borelSubgroup_le_suzukiGroup : borelSubgroup m ≤ suzukiGroup m := by
  refine sup_le ?_ (unipotentSubgroup_le_suzukiGroup m)
  rintro _ ⟨κ, rfl⟩
  exact torus_mem_suzukiGroup m κ

/-- **The Borel subgroup normalizes the unipotent subgroup.** -/
theorem borelSubgroup_le_normalizer :
    borelSubgroup m ≤ Subgroup.normalizer (unipotentSubgroup m : Set _) :=
  sup_le (range_torus_le_normalizer m) Subgroup.le_normalizer

/-- **The Weyl element conjugates `u(a, b)` into the Borel subgroup only when `u(a, b) = 1`.** -/
theorem weyl_mul_unipotent_mul_weyl_mem_borelSubgroup_iff {a b : GaloisField 2 (2 * m + 1)} :
    weyl m * unipotent m a b * weyl m ∈ borelSubgroup m ↔ a = 0 ∧ b = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨ha, hb⟩ ↦ mem_borelSubgroup.mpr ⟨1, 0, 0, by simp [ha, hb]⟩⟩
  obtain ⟨κ, c, d, h⟩ := mem_borelSubgroup.mp h
  -- Elements of `B` are lower triangular, while the last column of `w u(a, b) w` is the reversed
  -- first column `(u₃₀, a^(1+θ) + b, a, 1)` of `u(a, b)`.
  have h23 := congrArg
    (fun g : GL (Fin 4) (GaloisField 2 (2 * m + 1)) ↦
      (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) 2 3) h
  have h13 := congrArg
    (fun g : GL (Fin 4) (GaloisField 2 (2 * m + 1)) ↦
      (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) 1 3) h
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply] at h23 h13
  refine ⟨h23.symm, ?_⟩
  simpa [← h23] using h13.symm

/-- The Borel subgroup `B = H U`, inside the Suzuki group. -/
abbrev borelSubgroupOf : Subgroup (suzukiGroup m) :=
  (borelSubgroup m).subgroupOf (suzukiGroup m)

/-- The Borel subgroup normalizes the unipotent subgroup, inside the Suzuki group. -/
theorem borelSubgroupOf_le_normalizer :
    borelSubgroupOf m ≤ Subgroup.normalizer (unipotentSubgroupOf m : Set (suzukiGroup m)) :=
  fun x hx ↦ Subgroup.mem_normalizer_iff.mpr fun g ↦ by
    simpa [Subgroup.mem_subgroupOf] using
      Subgroup.mem_normalizer_iff.mp (borelSubgroup_le_normalizer m hx) g

/-- **The conjugates of the unipotent subgroup generate the Suzuki group.** The Weyl element is
`u(1, 1)⁻¹ (w u(0, 1) w⁻¹) u(1, 0)⁻¹`, by the rank-one Bruhat relation at the parameter `1`. -/
theorem normalClosure_unipotentSubgroupOf :
    Subgroup.normalClosure (unipotentSubgroupOf m : Set (suzukiGroup m)) = ⊤ := by
  set X := Subgroup.normalClosure (unipotentSubgroupOf m : Set (suzukiGroup m))
  have hU (a b : GaloisField 2 (2 * m + 1)) : (⟨_, unipotent_mem_suzukiGroup a b⟩ :
      suzukiGroup m) ∈ X :=
    Subgroup.subset_normalClosure
      (Subgroup.mem_subgroupOf.mpr (mem_unipotentSubgroup.mpr ⟨a, b, rfl⟩))
  have hrel : weyl m = (unipotent m 1 1)⁻¹ * (weyl m * unipotent m 0 1 * (weyl m)⁻¹) *
      (unipotent m 1 0)⁻¹ := by
    have h := weyl_mul_unipotent_zero_mul_weyl m 1 one_ne_zero
    simp only [one_pow, div_one, inv_one, Units.mk0_one, map_one, mul_one] at h
    rw [weyl_inv, h]
    group
  have hw : weylOf m ∈ X := by
    have h := mul_mem (mul_mem (inv_mem (hU 1 1))
      ((Subgroup.normalClosure_normal).conj_mem _ (hU 0 1) (weylOf m))) (inv_mem (hU 1 0))
    convert h using 1
    exact Subtype.ext hrel
  refine eq_top_iff.mpr fun g _ ↦ ?_
  have hle : suzukiGroup m ≤ X.map (suzukiGroup m).subtype :=
    suzukiGroup_le_iff.mpr ⟨fun a b ↦ ⟨_, hU a b, rfl⟩, ⟨_, hw, rfl⟩⟩
  obtain ⟨x, hx, hxg⟩ := hle g.2
  rwa [Subtype.ext hxg] at hx

end Suzuki

end TauCeti
