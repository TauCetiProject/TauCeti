/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalized

/-!
# The normalization of cubical chains

For a finite set `S` of coordinates, let `ζ_S : Iⁿ → Iⁿ` set the coordinates in `S` to `0`.  The
**normalization** of a singular `n`-cube `c` is the signed sum

`normalize c = Σ_S (-1) ^ |S| (c ∘ ζ_S)`,

that is, the image of `c` under the product of the commuting projections `1 - ζ_i`.  It is natural
in the space, it vanishes on degenerate cubes
(`CubicalChain.normalize_eq_zero_of_mem_degenerate`), and it differs from the identity by a
degenerate chain (`CubicalChain.normalize_sub_mem_degenerate`): every term with `S ≠ ∅` does not
depend on the coordinates in `S`.  So it induces a natural section
`NormalizedCubicalChain.toCubicalChain` of the quotient map from unnormalized to normalized chains.

Through this section, the normalized cubical `n`-chains are naturally a retract of the free module
on the singular `n`-cubes, that is, on the continuous maps from the model `Iⁿ`.  This is the form
in which the method of acyclic models applies to them.

## Main definitions

* `TauCeti.SingularCube.zeroOn`: the map `ζ_S` of the cube setting the coordinates in `S` to `0`.
* `TauCeti.CubicalChain.normalize`: the normalization of unnormalized cubical chains.
* `TauCeti.NormalizedCubicalChain.toCubicalChain`: the induced natural section of the quotient.

## Main results

* `TauCeti.CubicalChain.normalize_eq_zero_of_mem_degenerate`: normalization kills degenerate chains.
* `TauCeti.CubicalChain.normalize_sub_mem_degenerate`: normalization is the identity up to a
  degenerate chain.
* `TauCeti.NormalizedCubicalChain.mk_toCubicalChain`: the section is a section.
* `TauCeti.NormalizedCubicalChain.toCubicalChain_map`: the section is natural.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
-/

public section

noncomputable section

open Finsupp unitInterval

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace SingularCube

/-- The map of the cube `Iⁿ` setting the coordinates in `S` to `0`. -/
def zeroOn {n : ℕ} (S : Finset (Fin n)) : C(Fin n → I, Fin n → I) where
  toFun x j := if j ∈ S then 0 else x j
  continuous_toFun := continuous_pi fun j ↦ by split_ifs <;> fun_prop

@[simp]
theorem zeroOn_apply {n : ℕ} (S : Finset (Fin n)) (x : Fin n → I) (j : Fin n) :
    zeroOn S x j = if j ∈ S then 0 else x j :=
  (rfl)

@[simp]
theorem zeroOn_empty {n : ℕ} : zeroOn (∅ : Finset (Fin n)) = ContinuousMap.id _ := by
  ext x j
  simp

/-- A cube composed with `ζ_S` does not depend on the coordinates in `S`. -/
theorem isDegenerateAt_comp_zeroOn {n : ℕ} (c : SingularCube X n) {S : Finset (Fin n)}
    {j : Fin n} (hj : j ∈ S) : IsDegenerateAt (c.comp (zeroOn S)) j :=
  isDegenerateAt_iff.2 fun x t ↦ by
    simp only [ContinuousMap.comp_apply]
    congr 1
    ext i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi, Function.update_of_ne (show i ≠ j by rintro rfl; exact hi hj)]

/-- Setting one more coordinate, on which the cube does not depend, to `0` does not change the
cube. -/
theorem comp_zeroOn_insert {n : ℕ} {c : SingularCube X n} {j : Fin n} (h : IsDegenerateAt c j)
    (S : Finset (Fin n)) : c.comp (zeroOn (insert j S)) = c.comp (zeroOn S) := by
  ext x
  simp only [ContinuousMap.comp_apply]
  have : zeroOn (insert j S) x = Function.update (zeroOn S x) j 0 := by
    ext i
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [this, h.apply_update]

end SingularCube

namespace CubicalChain

open SingularCube

variable (R : Type*) [Ring R]

/-- The **normalization** of cubical chains: a cube `c` is sent to
`Σ_S (-1) ^ |S| (c ∘ ζ_S)`, where `ζ_S` sets the coordinates in `S` to `0`. -/
def normalize (n : ℕ) : CubicalChain X R n →ₗ[R] CubicalChain X R n :=
  linearCombination R fun c ↦
    ∑ S : Finset (Fin n), (-1 : R) ^ S.card • single (c.comp (zeroOn S)) (1 : R)

theorem normalize_single {n : ℕ} (c : SingularCube X n) (a : R) :
    normalize R n (single c a) =
      ∑ S : Finset (Fin n), (-1 : R) ^ S.card • single (c.comp (zeroOn S)) a := by
  have hc : ∀ i : ℕ, a * (-1 : R) ^ i = (-1) ^ i * a := fun i ↦
    ((Commute.neg_one_right a).pow_right i).eq
  simp only [normalize, linearCombination_single, Finset.smul_sum, smul_single, smul_eq_mul,
    mul_one, hc]

/-- Normalization is natural. -/
theorem map_normalize (f : C(X, Y)) {n : ℕ} (g : CubicalChain X R n) :
    map R f n (normalize R n g) = normalize R n (map R f n g) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g h hg hh => simp only [map_add, hg, hh]
  | single c a => simp [normalize_single, ContinuousMap.comp_assoc]

/-- Normalization kills a cube which does not depend on one of its coordinates: the terms for
`S` and for `S` with that coordinate added or removed cancel. -/
theorem normalize_single_eq_zero_of_isDegenerateAt {n : ℕ} {c : SingularCube X n} {j : Fin n}
    (h : IsDegenerateAt c j) (a : R) : normalize R n (single c a) = 0 := by
  classical
  rw [normalize_single]
  refine Finset.sum_involution (fun S _ ↦ if j ∈ S then S.erase j else insert j S)
    (fun S _ ↦ ?_) (fun S _ _ ↦ ?_) (fun _ _ ↦ Finset.mem_univ _) (fun S _ ↦ ?_)
  · split_ifs with hS
    · have hcard := Finset.card_erase_add_one hS
      rw [← comp_zeroOn_insert h (S.erase j), Finset.insert_erase hS, ← hcard, pow_succ,
        mul_neg_one, neg_smul, neg_add_cancel]
    · rw [comp_zeroOn_insert h, Finset.card_insert_of_notMem hS, pow_succ, mul_neg_one,
        neg_smul, add_neg_cancel]
  · split_ifs with hS
    · intro he
      rw [← he] at hS
      exact Finset.notMem_erase j S hS
    · exact fun he ↦ hS (he ▸ Finset.mem_insert_self j S)
  · by_cases hS : j ∈ S
    · simp [hS, Finset.insert_erase hS]
    · simp [hS, Finset.erase_insert hS]

/-- **Normalization kills degenerate chains.** -/
theorem normalize_eq_zero_of_mem_degenerate {n : ℕ} {f : CubicalChain X R n}
    (hf : f ∈ degenerate X R n) : normalize R n f = 0 := by
  refine degenerate_induction R (P := fun f ↦ normalize R n f = 0) (by simp) ?_ ?_ ?_ hf
  · intro c hc
    obtain ⟨j, hj⟩ := isDegenerate_iff.1 hc
    exact normalize_single_eq_zero_of_isDegenerateAt R hj 1
  · intro f g hf hg
    rw [map_add, hf, hg, add_zero]
  · intro r f hf
    rw [map_smul, hf, smul_zero]

/-- **Normalization is the identity up to a degenerate chain**: every term with `S ≠ ∅` does not
depend on the coordinates in `S`. -/
theorem normalize_sub_mem_degenerate {n : ℕ} (f : CubicalChain X R n) :
    normalize R n f - f ∈ degenerate X R n := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, add_sub_add_comm]
    exact Submodule.add_mem _ hf hg
  | single c a =>
    rw [normalize_single, ← Finset.add_sum_erase _ _ (Finset.mem_univ ∅), Finset.card_empty,
      pow_zero, one_smul, zeroOn_empty, ContinuousMap.comp_id, add_sub_cancel_left]
    refine Submodule.sum_mem _ fun S hS ↦ Submodule.smul_mem _ _ ?_
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hS)
    exact single_mem_degenerate R (isDegenerateAt_comp_zeroOn c hj).isDegenerate a

end CubicalChain

namespace NormalizedCubicalChain

open CubicalChain

variable (R : Type*) [Ring R]

variable (X) in
/-- The natural section of the quotient map from unnormalized to normalized cubical chains,
induced by the normalization. -/
def toCubicalChain (n : ℕ) : NormalizedCubicalChain X R n →ₗ[R] CubicalChain X R n :=
  Submodule.liftQ _ (normalize R n) fun _ hf ↦ normalize_eq_zero_of_mem_degenerate R hf

@[simp]
theorem toCubicalChain_mk {n : ℕ} (f : CubicalChain X R n) :
    toCubicalChain X R n (Submodule.Quotient.mk f) = normalize R n f :=
  Submodule.liftQ_apply _ _ f

/-- The section is a section of the quotient map. -/
@[simp]
theorem mk_toCubicalChain {n : ℕ} (f : NormalizedCubicalChain X R n) :
    Submodule.Quotient.mk (toCubicalChain X R n f) = f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [toCubicalChain_mk, Submodule.Quotient.eq]
    exact normalize_sub_mem_degenerate R f

/-- The section is natural. -/
theorem toCubicalChain_map (f : C(X, Y)) {n : ℕ} (g : NormalizedCubicalChain X R n) :
    toCubicalChain Y R n (map R f n g) = CubicalChain.map R f n (toCubicalChain X R n g) := by
  induction g using Submodule.Quotient.induction_on with
  | H g => rw [map_mk, toCubicalChain_mk, toCubicalChain_mk, map_normalize]

/-- A normalized chain is the combination of the classes of the cubes of its normalization. -/
theorem sum_toCubicalChain {n : ℕ} (f : NormalizedCubicalChain X R n) :
    (toCubicalChain X R n f).sum (fun c a ↦ a • ofCube X R c) = f := by
  conv_rhs => rw [← mk_toCubicalChain R f]
  induction toCubicalChain X R n f using Finsupp.induction_linear with
  | zero => simp
  | add g h hg hh =>
    rw [Finsupp.sum_add_index' (h := fun c a ↦ a • ofCube X R c) (fun _ ↦ zero_smul R _)
      (fun _ _ _ ↦ add_smul _ _ _), hg, hh, Submodule.Quotient.mk_add]
  | single c a =>
    rw [Finsupp.sum_single_index (h := fun c a ↦ a • ofCube X R c) (zero_smul R _),
      ofCube_def, ← Submodule.Quotient.mk_smul, smul_single_one]

end NormalizedCubicalChain

end TauCeti
