/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion

/-!
# The matrix of a cube-zero root subgroup

The matrix of a Kostant root subgroup at parameter `t` is the divided-power exponential
`∑ₖ tᵏ e⁽ᵏ⁾` of the root operator, read in the chosen lattice basis. When the operator squares to
zero this is `1 + t X` for the integral matrix `X` of the operator, which is
`TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_eq_one_add_smul`. This file treats the
next case, an operator that cubes to zero, where one more term survives:

```text
xᵢ(t) = 1 + t X + t² Y,
```

`Y` being the integral matrix of the divided square `e⁽²⁾ = e² / 2` on the lattice. This is the
shape of a simple root subgroup acting through a three-term weight string, such as a short root
subgroup of type `G₂` on the seven-dimensional module. The equation is proved on every
algebra-valued point and then read on the coordinate morphism, where it lets a consumer check a
matrix equation on all points of the root subgroup at once.

## Main results

Both live in the namespace `TauCeti.UniversalEnvelopingAlgebra`.

* `kostantRootSubgroupMatrix_eq_one_add_smul_add_smul`: the matrix of a cube-zero root subgroup
  at a point is `1 + t X + t² Y`.
* `exists_map_genericMatrix_kostantRootSubgroupCoordinateMap_eq_one_add_smul_add_smul`: the same
  equation on the generic matrix, along the root-subgroup coordinate morphism.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

section ClassThree

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]
variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable (i : ι)
variable (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {η : Type*} [Fintype η] [DecidableEq η] (b : Module.Basis η ℤ M)

/-- **The three-term divided-power expansion of a cube-zero root operator, read entrywise.** For a
root operator whose integral matrix is `X` and whose divided square has integral matrix `Y`, the
first three divided powers contribute the entries of `1`, `X` and `Y`, so the truncated
exponential sum at a parameter `t` has the entries of `1 + t X + t² Y`. -/
private theorem sum_range_three_repr_integralDividedPower {A : Type*} [CommRing A]
    (X Y : Matrix η η ℤ)
    (haction : ∀ s, ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : V) =
      ∑ r, X r s • (b r : V))
    (hsquare : ∀ s, Associative.dividedPower 2
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) (b s : V) = ∑ r, Y r s • (b r : V))
    (r s : η) (t : A) :
    ∑ k ∈ Finset.range 3,
        b.repr (integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M k
          (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i k hv)
          (b s)) r • t ^ k =
      ((1 : Matrix η η A) + t • X.map (Int.cast : ℤ → A) +
        t ^ 2 • Y.map (Int.cast : ℤ → A)) r s := by
  classical
  have hone : integralDividedPower
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M 1
      (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i 1 hv)
      (b s) = ∑ r, X r s • b r := by
    apply Subtype.ext
    rw [coe_integralDividedPower_apply, Associative.dividedPower_one, Module.End.smul_def,
      haction]
    push_cast
    simp
  have htwo : integralDividedPower
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M 2
      (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i 2 hv)
      (b s) = ∑ r, Y r s • b r := by
    apply Subtype.ext
    rw [coe_integralDividedPower_apply, Module.End.smul_def, hsquare]
    push_cast
    simp
  have hzero : integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M 0
      (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i 0 hv) = 1 :=
    integralDividedPower_zero _ _ _
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hone, htwo, hzero,
    Module.End.one_apply, congrFun (b.repr_sum_self fun q => X q s) r,
    congrFun (b.repr_sum_self fun q => Y q s) r, Module.Basis.repr_self]
  simp only [Finsupp.single_apply, pow_zero, pow_one, Matrix.add_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.map_apply, zsmul_eq_mul, smul_eq_mul, Int.cast_ite, Int.cast_one,
    Int.cast_zero]
  rcases eq_or_ne r s with rfl | hrs
  · simp [mul_comm]
  · simp [hrs, hrs.symm, mul_comm]

include hnil in
/-- **The matrix of a cube-zero root subgroup is `1 + t X + t² Y`.** When the root operator cubes
to zero its divided-power exponential stops after the quadratic term, so the root-subgroup matrix
at parameter `t` is the identity plus `t` times the integral matrix `X` of the operator plus `t²`
times the integral matrix `Y` of its divided square. -/
theorem kostantRootSubgroupMatrix_eq_one_add_smul_add_smul {A : Type*} [CommRing A]
    (X Y : Matrix η η ℤ)
    (hclass : nilpotencyClass
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) ≤ 3)
    (haction : ∀ s, ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : V) =
      ∑ r, X r s • (b r : V))
    (hsquare : ∀ s, Associative.dividedPower 2
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) (b s : V) = ∑ r, Y r s • (b r : V))
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    (kostantRootSubgroupMatrix e h ρ M hM i hnil b f).val =
      1 + Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) •
        X.map (Int.cast : ℤ → A) +
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) ^ 2 •
          Y.map (Int.cast : ℤ → A) := by
  ext r s
  -- Past the nilpotency class the divided powers vanish, so the exponential sum may be padded
  -- out to the three terms that the cube-zero truncation leaves.
  have hpad : ∑ k ∈ Finset.range
        (nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))),
      b.repr (integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M k
          (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i k hv)
          (b s)) r • Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) ^ k =
      ∑ k ∈ Finset.range 3,
        b.repr (integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M k
            (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i k hv)
            (b s)) r • Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) ^ k := by
    refine Finset.sum_subset (Finset.range_subset_range.2 hclass) fun k _ hk => ?_
    rw [Finset.mem_range, not_lt] at hk
    rw [integralDividedPower_eq_zero_of_le _ _ _ _ (pow_nilpotencyClass hnil) hk]
    simp
  rw [kostantRootSubgroupMatrix_apply, repr_kostantRootSubgroupPoints_baseChange, hpad]
  exact sum_range_three_repr_integralDividedPower e h ρ M hM i b X Y haction hsquare r s _

end ClassThree

section GenericMatrix

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type} [AddCommGroup V] [Module ℚ V]
variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable (i : ι)
variable (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {N : ℕ} (bb : Module.Basis (Fin N) ℤ M)

include hnil in
/-- **The generic matrix of a cube-zero root subgroup is `1 + t X + t² Y`.** This is
`TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_eq_one_add_smul_add_smul` read on
the coordinate morphism rather than on a point: the entries of the generic matrix of `GL N` are
carried to those of `1 + t X + t² Y` for the parameter `t` of the universal point of `𝔾ₐ`. -/
theorem exists_map_genericMatrix_kostantRootSubgroupCoordinateMap_eq_one_add_smul_add_smul
    (X Y : Matrix (Fin N) (Fin N) ℤ)
    (hclass : nilpotencyClass
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) ≤ 3)
    (haction : ∀ s, ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (bb s : V) =
      ∑ r, X r s • (bb r : V))
    (hsquare : ∀ s, Associative.dividedPower 2
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) (bb s : V) =
        ∑ r, Y r s • (bb r : V)) :
    ∃ t : AdditiveGroup.coordinateHopfAlgebra ℤ,
      (GeneralLinear.genericMatrix ℤ N).map
          (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil bb).hom.toAlgHom =
        1 + t • X.map (Int.cast : ℤ → AdditiveGroup.coordinateHopfAlgebra ℤ) +
          t ^ 2 • Y.map (Int.cast : ℤ → AdditiveGroup.coordinateHopfAlgebra ℤ) := by
  obtain ⟨q, hq⟩ :=
    exists_map_genericMatrix_eq_kostantRootSubgroupMatrix e h ρ M hM i hnil bb
  exact ⟨Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv q),
    hq.trans (kostantRootSubgroupMatrix_eq_one_add_smul_add_smul e h ρ M hM i hnil bb X Y hclass
      haction hsquare q)⟩

end GenericMatrix

end TauCeti.UniversalEnvelopingAlgebra
