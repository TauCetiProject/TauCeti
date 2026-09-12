/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType

/-!
# The Picard group of a numerical type

Let `T` be a numerical type, with components `i`, multiplicities `mᵢ`, weights `wᵢ` and
intersection matrix `A = (aᵢⱼ)`. A divisor class on the special fibre of a regular model
realising `T` is recorded by its multidegree: the tuple of the degrees of a line bundle on the
components, each taken over the constant field `κᵢ` of its own component. The degree over `κⱼ` of
the restriction to `Cⱼ` of the line bundle attached to `Cᵢ` is `aᵢⱼ / wⱼ`, so the classes coming
from the components themselves span the image of

`eᵢ ↦ ∑ⱼ (aᵢⱼ / wⱼ) eⱼ`,

and the Picard group of the numerical type is the cokernel of that map, as in
[Stacks, Tag 0C7H](https://stacks.math.columbia.edu/tag/0C7H).

The divisions `aᵢⱼ / wⱼ` are exact: the defining axiom of a numerical type gives `wⱼ ∣ aⱼᵢ`, and
the intersection matrix is symmetric. Performing them is not cosmetic. The cokernel `Coker(A)` of
the intersection matrix itself is a *different* group, and the comparison map `Pic(T) → Coker(A)`
induced by `eⱼ ↦ wⱼeⱼ` is injective but, as soon as one weight exceeds one, not surjective. Both
halves of that statement are proved below.

## Main definitions

* `TauCeti.NumericalType.weightedIntersection`: the matrix `a'ᵢⱼ = aᵢⱼ / wⱼ`.
* `TauCeti.NumericalType.principalDivisors`: the subgroup of multidegrees spanned by the rows of
  `A'`, and `TauCeti.NumericalType.intersectionRelations`, the subgroup spanned by the rows of `A`
  itself.
* `TauCeti.NumericalType.Pic`: the Picard group of a numerical type, the cokernel of `A'`, and
  `TauCeti.NumericalType.Coker`, the cokernel of `A`.
* `TauCeti.NumericalType.picToCoker`: the comparison map `Pic(T) → Coker(A)` induced by
  `eⱼ ↦ wⱼeⱼ`.
* `TauCeti.NumericalType.degree`: the total degree `∑ⱼ mⱼwⱼdⱼ` of a divisor class, the degree over
  the residue field of the corresponding line bundle on the whole special fibre.
* `TauCeti.NumericalType.Equiv.picCongr`: the isomorphism of Picard groups induced by an
  equivalence of numerical types.

## Main results

* `TauCeti.NumericalType.picToCoker_injective`: the comparison map is injective, which is the
  assertion of [Stacks, Tag 0CE7](https://stacks.math.columbia.edu/tag/0CE7).
* `TauCeti.NumericalType.picToCoker_surjective_iff`: it is surjective exactly when every weight is
  one, so `Pic(T)` is a strictly finer invariant than `Coker(A)`.
* `TauCeti.NumericalType.smul_ne_zero_of_degree_ne_zero`: a class of nonzero total degree has
  infinite order, and `TauCeti.NumericalType.smul_mk_single_ne_zero`, its special case for the
  class of the unit multidegree supported at a component, whose total degree is `mᵢwᵢ ≠ 0`. With
  the finite generation that `Pic(T)` inherits from `ℤ^Component` this is half of the assertion
  that `Pic(T)` is finitely generated of rank one.
* `TauCeti.NumericalType.Equiv.picCongr` and `TauCeti.NumericalType.Equiv.degree_picCongr`: the
  Picard group and the total degree do not depend on the chosen indexing of the components.

## Implementation notes

Multidegrees are plain functions `T.Component → ℤ`, and the two relation subgroups are ranges of
`Matrix.vecMulLinear`, so `Pic(T)` and `Coker(A)` are literally cokernels of `ℤ`-linear maps and
inherit their module structure from `Submodule.Quotient`. Invariance under reindexing of the
component set, in the sense of `TauCeti.NumericalType.reindex`, is the special case of
`TauCeti.NumericalType.Equiv.picCongr` at `TauCeti.NumericalType.equivReindex`; it is transport
along `LinearEquiv.funCongrLeft`.
-/

public section

namespace TauCeti

open Finset Matrix

namespace NumericalType

universe u v w

variable (T : NumericalType.{u})

/-! ### The weighted intersection matrix -/

/-- The weight of the `j`-th component divides every intersection number `aᵢⱼ`.

The axiom `weight_dvd` of a numerical type says that `wⱼ` divides every entry of the `j`-th
*row*; symmetry of the intersection matrix turns that into divisibility of the `j`-th column. -/
lemma weight_dvd_intersection (i j : T.Component) : (T.weight j : ℤ) ∣ T.intersection i j := by
  rw [T.intersection_comm]
  exact T.weight_dvd j i

/-- The weighted intersection matrix `a'ᵢⱼ = aᵢⱼ / wⱼ` of a numerical type. Its `i`-th row is the
multidegree of the line bundle attached to the `i`-th component: the `j`-th entry is the degree,
over the constant field `κⱼ` of the `j`-th component, of the restriction of that bundle to `Cⱼ`.

The division is exact by `TauCeti.NumericalType.weight_dvd_intersection`; see
`TauCeti.NumericalType.weightedIntersection_mul_weight`. -/
def weightedIntersection : Matrix T.Component T.Component ℤ :=
  .of fun i j ↦ T.intersection i j / (T.weight j : ℤ)

/-- The entries of the weighted intersection matrix. -/
@[simp]
lemma weightedIntersection_apply (i j : T.Component) :
    T.weightedIntersection i j = T.intersection i j / (T.weight j : ℤ) := (rfl)

/-- The division defining the weighted intersection matrix is exact. -/
@[simp]
lemma weightedIntersection_mul_weight (i j : T.Component) :
    T.weightedIntersection i j * (T.weight j : ℤ) = T.intersection i j :=
  Int.ediv_mul_cancel (T.weight_dvd_intersection i j)

/-- Rescaling the columns of the weighted intersection matrix by the weights returns the
intersection matrix. -/
lemma weightedIntersection_mul_diagonal :
    T.weightedIntersection * Matrix.diagonal (fun i ↦ (T.weight i : ℤ)) = T.intersection := by
  ext i j
  rw [Matrix.mul_diagonal, weightedIntersection_mul_weight]

/-! ### Multidegrees and the two relation subgroups -/

/-- Rescaling the `j`-th coordinate of a multidegree by the weight `wⱼ`, that is, the map
`eⱼ ↦ wⱼeⱼ`. It converts a degree measured over the constant field `κⱼ` into a degree measured
over the residue field. -/
def weightScaling : (T.Component → ℤ) →ₗ[ℤ] T.Component → ℤ :=
  (Matrix.diagonal fun i ↦ (T.weight i : ℤ)).vecMulLinear

/-- The coordinates of a weight-rescaled multidegree. -/
@[simp]
lemma weightScaling_apply (d : T.Component → ℤ) (j : T.Component) :
    T.weightScaling d j = d j * (T.weight j : ℤ) :=
  Matrix.vecMul_diagonal _ _ _

private lemma weight_ne_zero (j : T.Component) : (T.weight j : ℤ) ≠ 0 :=
  (Int.natCast_pos.mpr (T.weight j).pos).ne'

/-- Rescaling by the weights is injective, the weights being positive. -/
lemma weightScaling_injective : Function.Injective T.weightScaling := fun _ _ h ↦
  funext fun j ↦ mul_right_cancel₀ (T.weight_ne_zero j) (by simpa using congrFun h j)

/-- Rescaling by the weights carries the rows of the weighted intersection matrix to the rows of
the intersection matrix, at the level of the linear maps they induce. -/
lemma weightScaling_comp_weightedIntersection :
    T.weightScaling ∘ₗ T.weightedIntersection.vecMulLinear = T.intersection.vecMulLinear :=
  LinearMap.ext fun d ↦ by
    rw [LinearMap.comp_apply, Matrix.vecMulLinear_apply, weightScaling, Matrix.vecMulLinear_apply,
      Matrix.vecMul_vecMul, weightedIntersection_mul_diagonal, Matrix.vecMulLinear_apply]

/-- The principal multidegrees of a numerical type: the subgroup spanned by the rows
`j ↦ aᵢⱼ / wⱼ` of the weighted intersection matrix, that is, by the multidegrees of the line
bundles attached to the components. -/
def principalDivisors : Submodule ℤ (T.Component → ℤ) :=
  LinearMap.range T.weightedIntersection.vecMulLinear

/-- The subgroup spanned by the rows of the intersection matrix itself, the unweighted analogue of
`TauCeti.NumericalType.principalDivisors`. -/
def intersectionRelations : Submodule ℤ (T.Component → ℤ) :=
  LinearMap.range T.intersection.vecMulLinear

/-- Membership in the principal multidegrees, spelled out. -/
lemma mem_principalDivisors_iff {d : T.Component → ℤ} :
    d ∈ T.principalDivisors ↔ ∃ v, v ᵥ* T.weightedIntersection = d :=
  LinearMap.mem_range

/-- Membership in the span of the rows of the intersection matrix, spelled out. -/
lemma mem_intersectionRelations_iff {d : T.Component → ℤ} :
    d ∈ T.intersectionRelations ↔ ∃ v, v ᵥ* T.intersection = d :=
  LinearMap.mem_range

/-- Rescaling by the weights carries the principal multidegrees exactly onto the span of the rows
of the intersection matrix. -/
lemma map_weightScaling_principalDivisors :
    T.principalDivisors.map T.weightScaling = T.intersectionRelations := by
  rw [principalDivisors, ← LinearMap.range_comp, weightScaling_comp_weightedIntersection,
    intersectionRelations]

/-- Every row of the intersection matrix is divisible by the weights, so the relations it spans
are themselves weight-rescaled multidegrees. -/
lemma intersectionRelations_le_range_weightScaling :
    T.intersectionRelations ≤ LinearMap.range T.weightScaling := by
  rw [← map_weightScaling_principalDivisors]
  exact LinearMap.map_le_range

/-- Rescaling by the weights descends to the quotients defining `Pic(T)` and `Coker(A)`. -/
lemma principalDivisors_le_comap_intersectionRelations :
    T.principalDivisors ≤ T.intersectionRelations.comap T.weightScaling :=
  Submodule.map_le_iff_le_comap.mp T.map_weightScaling_principalDivisors.le

/-! ### The Picard group and the cokernel of the intersection matrix -/

/-- The Picard group of a numerical type: the cokernel of `eᵢ ↦ ∑ⱼ (aᵢⱼ/wⱼ)eⱼ`, as in
[Stacks, Tag 0C7H](https://stacks.math.columbia.edu/tag/0C7H). Its elements are multidegrees of
line bundles on the special fibre modulo those coming from the components. -/
abbrev Pic := (T.Component → ℤ) ⧸ T.principalDivisors

/-- The cokernel of the intersection matrix of a numerical type. It is a coarser invariant than
`TauCeti.NumericalType.Pic`; see `TauCeti.NumericalType.picToCoker_surjective_iff`. -/
abbrev Coker := (T.Component → ℤ) ⧸ T.intersectionRelations

/-- The comparison map `Pic(T) → Coker(A)` induced by `eⱼ ↦ wⱼeⱼ`, from
[Stacks, Tag 0CE7](https://stacks.math.columbia.edu/tag/0CE7). -/
def picToCoker : T.Pic →ₗ[ℤ] T.Coker :=
  Submodule.mapQ _ _ T.weightScaling T.principalDivisors_le_comap_intersectionRelations

/-- The comparison map on the class of a multidegree. -/
@[simp]
lemma picToCoker_mk (d : T.Component → ℤ) :
    T.picToCoker (Submodule.Quotient.mk d) = Submodule.Quotient.mk (T.weightScaling d) := (rfl)

/-- The comparison map of [Stacks, Tag 0CE7](https://stacks.math.columbia.edu/tag/0CE7) is
injective: a multidegree whose weight rescaling is a combination of the rows of `A` is itself the
same combination of the rows of `A'`. -/
theorem picToCoker_injective : Function.Injective T.picToCoker := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H d =>
    rw [picToCoker_mk, Submodule.Quotient.mk_eq_zero, mem_intersectionRelations_iff] at hx
    obtain ⟨v, hv⟩ := hx
    refine (Submodule.Quotient.mk_eq_zero _).2 (T.mem_principalDivisors_iff.2 ⟨v, ?_⟩)
    refine T.weightScaling_injective ?_
    rw [← Matrix.vecMulLinear_apply, ← LinearMap.comp_apply,
      weightScaling_comp_weightedIntersection, Matrix.vecMulLinear_apply, hv]

/-- The image of the comparison map consists of the classes of the weight-rescaled
multidegrees. -/
lemma range_picToCoker :
    LinearMap.range T.picToCoker =
      (LinearMap.range T.weightScaling).map T.intersectionRelations.mkQ :=
  Submodule.range_mapQ _ _ _ _

/-- The comparison map `Pic(T) → Coker(A)` is surjective exactly when every component has weight
one, that is, exactly when no division by a weight took place. So the weighted cokernel is a
strictly finer invariant than the cokernel of the intersection matrix. -/
theorem picToCoker_surjective_iff :
    Function.Surjective T.picToCoker ↔ ∀ i, T.weight i = 1 := by
  rw [← LinearMap.range_eq_top, range_picToCoker, Submodule.map_mkQ_eq_top,
    sup_eq_right.mpr T.intersectionRelations_le_range_weightScaling]
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨d, hd⟩ : Pi.single i (1 : ℤ) ∈ LinearMap.range T.weightScaling := h ▸ Submodule.mem_top
    have hdi : d i * (T.weight i : ℤ) = 1 := by simpa using congrFun hd i
    have hdvd : (T.weight i : ℕ) ∣ 1 := by
      have hz : ((T.weight i : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ) := by
        simpa using Dvd.intro_left (d i) hdi
      exact_mod_cast hz
    exact PNat.coe_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  · rw [LinearMap.range_eq_top]
    exact fun y ↦ ⟨y, funext fun j ↦ by simp [h j]⟩

/-! ### The total degree -/

/-- The total degree `∑ⱼ mⱼwⱼdⱼ` of a multidegree `d`, before passing to the Picard group.

Geometrically this is the degree over the residue field of a line bundle on the whole special
fibre `∑ⱼ mⱼCⱼ`: the `j`-th component contributes its multiplicity times the degree of the
restriction, measured over the residue field rather than over the constant field `κⱼ`. -/
def totalDegree : (T.Component → ℤ) →ₗ[ℤ] ℤ :=
  Fintype.linearCombination ℤ fun j ↦ (T.multiplicity j : ℤ) * (T.weight j : ℤ)

/-- The total degree, written out as a sum over the components. -/
lemma totalDegree_apply (d : T.Component → ℤ) :
    T.totalDegree d = ∑ j, d j * ((T.multiplicity j : ℤ) * (T.weight j : ℤ)) := by
  simp [totalDegree, Fintype.linearCombination_apply]

/-- The total degree kills the multidegrees coming from the components: this is exactly the fibre
relation `∑ⱼ mⱼaᵢⱼ = 0` of a numerical type. -/
lemma totalDegree_comp_weightedIntersection :
    T.totalDegree ∘ₗ T.weightedIntersection.vecMulLinear = 0 := by
  refine LinearMap.ext fun v ↦ ?_
  rw [LinearMap.comp_apply, Matrix.vecMulLinear_apply, totalDegree_apply, LinearMap.zero_apply]
  simp only [Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have key : ∀ j, v i * T.weightedIntersection i j * ((T.multiplicity j : ℤ) * (T.weight j : ℤ))
      = v i * ((T.multiplicity j : ℤ) * T.intersection i j) := fun j ↦ by
    rw [← T.weightedIntersection_mul_weight i j]
    ring
  rw [Finset.sum_congr rfl fun j _ ↦ key j, ← Finset.mul_sum, T.fiber_relation i, mul_zero]

/-- The total degree of a divisor class on a numerical type: the degree over the residue field of
the corresponding line bundle on the whole special fibre. -/
def degree : T.Pic →ₗ[ℤ] ℤ :=
  Submodule.liftQ _ T.totalDegree <| by
    rw [principalDivisors, LinearMap.range_le_ker_iff]
    exact T.totalDegree_comp_weightedIntersection

/-- The degree of the class of a multidegree is its total degree. -/
@[simp]
lemma degree_mk (d : T.Component → ℤ) :
    T.degree (Submodule.Quotient.mk d) = T.totalDegree d := (rfl)

/-- A divisor class of nonzero total degree has infinite order in `Pic(T)`: no nonzero multiple of
it vanishes. -/
theorem smul_ne_zero_of_degree_ne_zero {x : T.Pic} (hx : T.degree x ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    n • x ≠ 0 := by
  intro h
  have hdeg : n * T.degree x = 0 := by
    have := congrArg T.degree h
    rwa [map_smul, map_zero, smul_eq_mul] at this
  exact (mul_eq_zero.mp hdeg).elim hn hx

/-- No nonzero multiple of the class of the unit multidegree supported at the `i`-th component
vanishes in `Pic(T)`, because its total degree is `mᵢwᵢ ≠ 0`. This class is not the class of the
`i`-th component itself: that is the `i`-th row of the weighted intersection matrix, hence
principal and zero in `Pic(T)`.

Together with the finite generation that `Pic(T)` inherits from `ℤ^Component`, this is half of the
assertion that `Pic(T)` is a finitely generated abelian group of rank one. -/
theorem smul_mk_single_ne_zero (i : T.Component) {n : ℤ} (hn : n ≠ 0) :
    n • (Submodule.Quotient.mk (Pi.single i 1) : T.Pic) ≠ 0 := by
  refine T.smul_ne_zero_of_degree_ne_zero ?_ hn
  rw [degree_mk, totalDegree, Fintype.linearCombination_apply_single, smul_eq_mul, one_mul]
  exact mul_ne_zero (Int.natCast_pos.mpr (T.multiplicity i).pos).ne' (T.weight_ne_zero i)

/-! ### Invariance under equivalences of numerical types -/

namespace Equiv

variable {T} {T' : NumericalType.{v}} {T'' : NumericalType.{w}}

/-- An equivalence of numerical types matches the weighted intersection matrices. -/
lemma weightedIntersection_eq (f : T.Equiv T') :
    T'.weightedIntersection = T.weightedIntersection.submatrix f.toEquiv.symm f.toEquiv.symm := by
  ext a b
  have hA := f.intersection_apply (f.toEquiv.symm a) (f.toEquiv.symm b)
  have hw := f.weight_apply (f.toEquiv.symm b)
  rw [_root_.Equiv.apply_symm_apply, _root_.Equiv.apply_symm_apply] at hA
  rw [_root_.Equiv.apply_symm_apply] at hw
  rw [Matrix.submatrix_apply, weightedIntersection_apply, weightedIntersection_apply, hA, hw]

/-- Transporting multidegrees along an equivalence of numerical types intertwines the two maps
whose cokernels are the Picard groups. -/
lemma vecMulLinear_weightedIntersection (f : T.Equiv T') :
    T'.weightedIntersection.vecMulLinear =
      (LinearEquiv.funCongrLeft ℤ ℤ f.toEquiv.symm : (T.Component → ℤ) →ₗ[ℤ] T'.Component → ℤ) ∘ₗ
        T.weightedIntersection.vecMulLinear ∘ₗ
        (LinearEquiv.funCongrLeft ℤ ℤ f.toEquiv : (T'.Component → ℤ) →ₗ[ℤ] T.Component → ℤ) := by
  refine LinearMap.ext fun v ↦ funext fun b ↦ ?_
  rw [f.weightedIntersection_eq]
  simp [Matrix.submatrix_vecMul_equiv, LinearMap.funLeft, Function.comp_def]

/-- An equivalence of numerical types matches the principal multidegrees. -/
lemma map_principalDivisors (f : T.Equiv T') :
    T.principalDivisors.map
        (LinearEquiv.funCongrLeft ℤ ℤ f.toEquiv.symm : (T.Component → ℤ) →ₗ[ℤ] T'.Component → ℤ) =
      T'.principalDivisors := by
  have hT' : T'.principalDivisors =
      LinearMap.range
        ((LinearEquiv.funCongrLeft ℤ ℤ f.toEquiv.symm :
            (T.Component → ℤ) →ₗ[ℤ] T'.Component → ℤ) ∘ₗ
          T.weightedIntersection.vecMulLinear ∘ₗ
          (LinearEquiv.funCongrLeft ℤ ℤ f.toEquiv : (T'.Component → ℤ) →ₗ[ℤ] T.Component → ℤ)) := by
    rw [principalDivisors, f.vecMulLinear_weightedIntersection]
  rw [hT', LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    principalDivisors]

/-- Equivalent numerical types have isomorphic Picard groups. -/
def picCongr (f : T.Equiv T') : T.Pic ≃ₗ[ℤ] T'.Pic :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.funCongrLeft ℤ ℤ f.toEquiv.symm) f.map_principalDivisors

/-- The transported Picard class of a multidegree is the class of the transported
multidegree. -/
@[simp]
lemma picCongr_mk (f : T.Equiv T') (d : T.Component → ℤ) :
    f.picCongr (Submodule.Quotient.mk d) =
      Submodule.Quotient.mk (fun b ↦ d (f.toEquiv.symm b)) := (rfl)

/-- The identity equivalence induces the identity of Picard groups. -/
@[simp]
lemma picCongr_refl : (refl : T.Equiv T).picCongr = LinearEquiv.refl ℤ T.Pic := by
  unfold picCongr
  simp only [refl_toEquiv, _root_.Equiv.refl_symm, LinearEquiv.funCongrLeft_id]
  rw [Submodule.Quotient.equiv_refl]
  apply LinearEquiv.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H d => rfl

/-- A composite of equivalences induces the composite isomorphism of Picard groups. -/
@[simp]
lemma picCongr_trans (f : T.Equiv T') (g : T'.Equiv T'') :
    (f.trans g).picCongr = f.picCongr.trans g.picCongr := by
  unfold picCongr
  simp only [trans_toEquiv, _root_.Equiv.symm_trans, LinearEquiv.funCongrLeft_comp]
  rw [Submodule.Quotient.equiv_trans]

/-- The inverse of an equivalence induces the inverse isomorphism of Picard groups. -/
@[simp]
lemma picCongr_symm (f : T.Equiv T') : f.picCongr.symm = f.symm.picCongr := by
  unfold picCongr
  rw [Submodule.Quotient.equiv_symm]
  simp only [symm_toEquiv, LinearEquiv.funCongrLeft_symm, _root_.Equiv.symm_symm]

/-- The total degree of a divisor class on a numerical type is an invariant of its equivalence
class. -/
@[simp]
lemma degree_picCongr (f : T.Equiv T') (x : T.Pic) : T'.degree (f.picCongr x) = T.degree x := by
  induction x using Submodule.Quotient.induction_on with
  | H d =>
    rw [picCongr_mk, degree_mk, degree_mk, totalDegree_apply, totalDegree_apply]
    refine (Fintype.sum_equiv f.toEquiv _ _ fun i ↦ ?_).symm
    simp

end Equiv

end NumericalType

end TauCeti
