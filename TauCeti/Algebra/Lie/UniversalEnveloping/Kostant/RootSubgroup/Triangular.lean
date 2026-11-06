/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Coordinate
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic

/-!
# Triangularity of positive Kostant root subgroups

Let `M` be a Kostant-stable integral lattice with a basis of Cartan weight vectors. If the basis
is ordered so that adding a positive multiple of a root moves strictly towards the beginning,
then every divided power of the corresponding root operator is strictly upper triangular away
from degree zero. Consequently its divided-power exponential is upper unitriangular over every
commutative base ring.

This realizes a positive Kostant root subgroup inside the upper-unitriangular group. It is the
matrix input needed to place the positive-root subgroup in the unipotent radical of a Borel
subgroup in the Chevalley--Demazure construction.

## Main declarations

* `kostantRootSubgroupMatrix_apply_eq_one_apply_of_forall_weight_ne`:
  an entry is that of the identity if no positive root multiple connects its two weights.
* `TauCeti.UniversalEnvelopingAlgebra.repr_integralDividedPower_eq_zero_of_not_lt`: positive
  divided powers have no coordinate on or below their source basis vector.
* `TauCeti.UniversalEnvelopingAlgebra.isUpperUnitriangular_kostantRootSubgroupMatrix`: a positive
  root-subgroup point has an upper-unitriangular matrix over every commutative ring.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupUpperUnitriangular`: the root-subgroup
  homomorphism corestricted to the upper-unitriangular group.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§21, 26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable {i : ι} {α : κ → ℤ}
variable {η : Type*} [Fintype η] [LinearOrder η]
variable (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)

/-! ## Integral divided-power coordinates -/

omit [Fintype η] [LinearOrder η] in
include e hM in
/-- A divided power has zero coordinate at a basis vector whose weight is not the corresponding
root shift of the source weight. No ordering or positivity hypothesis is needed. -/
theorem repr_integralDividedPower_eq_zero_of_weight_ne
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    {r s : η} {n : ℕ} (hrs : wt r ≠ wt s + n • α) :
    b.repr
        (integralDividedPower
          (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M n
          (fun _ hv ↦ dividedPower_apply_mem_of_kostantForm_apply_mem
            e h ρ hM i n hv) (b s)) r = 0 := by
  apply repr_eq_zero_of_isCartanWeightVector h ρ M b wt hwt
  · rw [coe_integralDividedPower_apply]
    exact IsCartanWeightVector.integralDividedPower e hα (hwt s) n
  · exact hrs

omit [Fintype η] in
include e hM in
/-- A positive divided power has no coordinate at a basis vector which does not precede its
source. The order hypothesis says precisely that a nonzero positive root shift of weights must
move from `s` to an index `r < s`.

This statement includes both the entries below the diagonal and the diagonal entries of every
positive-degree divided power. -/
theorem repr_integralDividedPower_eq_zero_of_not_lt
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (horder : ∀ {r s : η} {n : ℕ}, 0 < n → wt r = wt s + n • α → r < s)
    {r s : η} (hrs : ¬ r < s) {n : ℕ} (hn : 0 < n) :
    b.repr
        (integralDividedPower
          (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M n
          (fun _ hv ↦ dividedPower_apply_mem_of_kostantForm_apply_mem
            e h ρ hM i n hv) (b s)) r = 0 := by
  exact repr_integralDividedPower_eq_zero_of_weight_ne e h ρ M hM b wt hwt hα
    (fun heq ↦ hrs (horder hn heq))

include e hM in
/-- Every positive divided power of a positive root operator is upper triangular in an
ordered weight basis. -/
theorem isUpperTriangular_toMatrix_integralDividedPower
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (horder : ∀ {r s : η} {n : ℕ}, 0 < n → wt r = wt s + n • α → r < s)
    {n : ℕ} (hn : 0 < n) :
    (LinearMap.toMatrix b b
        (integralDividedPower
          (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M n
          (fun _ hv ↦ dividedPower_apply_mem_of_kostantForm_apply_mem
            e h ρ hM i n hv))).IsUpperTriangular := by
  intro r s hsr
  rw [LinearMap.toMatrix_apply]
  exact repr_integralDividedPower_eq_zero_of_not_lt e h ρ M hM b wt hwt hα horder
    (not_lt_of_ge hsr.le) hn

/-! ## Positive root-subgroup matrices -/

variable (i : ι)
variable (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))

omit [LinearOrder η] in
include e hM in
/-- A root-subgroup matrix agrees with the identity at an entry where no positive multiple of its
root connects the source and target weights. No ordering or positivity of the root is needed. -/
theorem kostantRootSubgroupMatrix_apply_eq_one_apply_of_forall_weight_ne [DecidableEq η]
    {A : Type*} [CommRing A]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) {r s : η}
    (hrs : ∀ n : ℕ, 0 < n → wt r ≠ wt s + n • α) :
    kostantRootSubgroupMatrix e h ρ M hM i hnil b f r s = (1 : Matrix η η A) r s := by
  classical
  let X (n : ℕ) := LinearMap.toMatrix b b
    (integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M n
      (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv))
  have hX (n : ℕ) (hn : 0 < n) : X n r s = 0 := by
    dsimp only [X]
    rw [LinearMap.toMatrix_apply]
    exact repr_integralDividedPower_eq_zero_of_weight_ne e h ρ M hM b wt hwt hα (hrs n hn)
  have hX0 : X 0 = 1 := by simp [X, integralDividedPower_zero, LinearMap.toMatrix_one]
  have hsum := kostantRootSubgroupMatrix_eq_sum e h ρ M hM i hnil b
    (nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) + 1) X (by omega)
    (fun n _ s => by simp [X, LinearMap.toMatrix_apply]) f
  rw [hsum, Finset.sum_range_succ', hX0]
  simp only [pow_zero, one_smul, Matrix.map_one Int.cast Int.cast_zero Int.cast_one,
    Matrix.add_apply, Matrix.one_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply]
  simp [hX]

include e hM in
/-- A positive Kostant root-subgroup point is upper unitriangular in an ordered weight basis over
every commutative base ring. The positive-degree divided powers are strictly upper triangular,
while the degree-zero divided power supplies the identity diagonal. -/
theorem isUpperUnitriangular_kostantRootSubgroupMatrix {A : Type*} [CommRing A]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (horder : ∀ {r s : η} {n : ℕ}, 0 < n → wt r = wt s + n • α → r < s)
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ((kostantRootSubgroupMatrix e h ρ M hM i hnil b f :
        Matrix.GeneralLinearGroup η A) : Matrix η η A).IsUpperUnitriangular := by
  have hentry {r s : η} (hrs : ¬ r < s) :=
    kostantRootSubgroupMatrix_apply_eq_one_apply_of_forall_weight_ne
      e h ρ M hM b wt i hnil hwt hα f (r := r) (s := s)
      (fun n hn heq ↦ hrs (horder hn heq))
  rw [Matrix.isUpperUnitriangular_def]
  constructor
  · intro r s hsr
    exact (hentry (r := r) (s := s) (not_lt_of_ge hsr.le)).trans
      (Matrix.one_apply_ne (ne_of_gt hsr))
  · intro r
    rw [hentry (lt_irrefl r), Matrix.one_apply_eq]

include e hM in
/-- The image of a positive Kostant root subgroup lies in the upper-unitriangular subgroup of
the ambient general linear group. -/
theorem range_kostantRootSubgroupMatrix_le_upperUnitriangular {A : Type*} [CommRing A]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (horder : ∀ {r s : η} {n : ℕ}, 0 < n → wt r = wt s + n • α → r < s) :
    (kostantRootSubgroupMatrix e h ρ M hM i hnil b (A := A)).range ≤
      upperUnitriangularGroup η A := by
  rintro g ⟨f, rfl⟩
  exact UpperUnitriangularGroup.mem_iff.mpr <|
    isUpperUnitriangular_kostantRootSubgroupMatrix
      e h ρ M hM b wt i hnil hwt hα horder f

include e hM in
/-- A positive Kostant root subgroup, with its codomain restricted to the upper-unitriangular
group. This is the root-radical form used in triangular Borel constructions. -/
noncomputable def kostantRootSubgroupUpperUnitriangular {A : Type*} [CommRing A]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (horder : ∀ {r s : η} {n : ℕ}, 0 < n → wt r = wt s + n • α → r < s) :
    WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A) →*
      upperUnitriangularGroup η A :=
  (kostantRootSubgroupMatrix e h ρ M hM i hnil b).codRestrict
    (upperUnitriangularGroup η A) fun f ↦
      range_kostantRootSubgroupMatrix_le_upperUnitriangular
        e h ρ M hM b wt i hnil hwt hα horder ⟨f, rfl⟩

/-- Forgetting the upper-unitriangular codomain recovers the original root-subgroup matrix. -/
@[simp]
theorem coe_kostantRootSubgroupUpperUnitriangular {A : Type*} [CommRing A]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (horder : ∀ {r s : η} {n : ℕ}, 0 < n → wt r = wt s + n • α → r < s)
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    (kostantRootSubgroupUpperUnitriangular
        e h ρ M hM b wt i hnil hwt hα horder f : Matrix.GeneralLinearGroup η A) =
      kostantRootSubgroupMatrix e h ρ M hM i hnil b f :=
  by rw [kostantRootSubgroupUpperUnitriangular, MonoidHom.codRestrict_apply]

/-- The upper-unitriangular realization of a positive Kostant root subgroup is natural in the
commutative base ring. -/
@[simp]
theorem map_kostantRootSubgroupUpperUnitriangular {A B : Type*} [CommRing A] [CommRing B]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (horder : ∀ {r s : η} {n : ℕ}, 0 < n → wt r = wt s + n • α → r < s)
    (φ : A →+* B) (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    UpperUnitriangularGroup.map φ
        (kostantRootSubgroupUpperUnitriangular
          e h ρ M hM b wt i hnil hwt hα horder f) =
      kostantRootSubgroupUpperUnitriangular
        e h ρ M hM b wt i hnil hwt hα horder
          (AlgHom.mapValue (H := SymmetricAlgebra ℤ ℤ) φ.toIntAlgHom f) := by
  apply Subtype.ext
  rw [UpperUnitriangularGroup.coe_map]
  exact map_kostantRootSubgroupMatrix e h ρ M hM i hnil b φ f

end TauCeti.UniversalEnvelopingAlgebra
