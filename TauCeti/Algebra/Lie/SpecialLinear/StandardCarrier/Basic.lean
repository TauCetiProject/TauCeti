/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.Algebra.Lie.Sl2.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.CoordinateLattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Relations
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Torus
public import TauCeti.Algebra.Lie.UniversalEnveloping.MatrixRepresentation
import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.RootInToral

/-!
# The full-weight Chevalley carrier of type `A`

Fix `r` and let `sl_{r+1}` act on the standard module `Fin (r+1) → ℚ`. This file feeds that
representation, its coordinate `ℤ`-lattice and the Bourbaki-numbered Chevalley generators

```text
e_i = E_{i,i+1},    f_i = E_{i+1,i},    h_i = E_{i,i} - E_{i+1,i+1}
```

into the Kostant toral-closure construction, and so produces an explicit affine group scheme over
`ℤ` for every rank: `TauCeti.SlStd.groupScheme`, the smallest closed subgroup scheme of `GL_{r+1}`
containing the divided-power exponential root subgroups of those generators together with the
weight torus of the standard lattice.

What distinguishes the standard module from the adjoint one is its weights. The Cartan generator
`h_i` acts on the coordinate vector at `k` by `δ_{k,i} - δ_{k,i+1}`, so the weights are the `ε_k`,
and `TauCeti.SlStd.span_range_weight_eq_top` says they generate the *whole* character lattice
`Fin r → ℤ` of the rank-`r` split torus, whose cocharacter lattice is spanned by the simple
coroots. That character lattice is the weight lattice `P` of type `A_r`, whereas the weights of the
adjoint module generate only the root lattice `Q`, of index `r + 1` in it. Consequently the split
torus of rank `r` is a *closed* subgroup of the carrier built here
(`TauCeti.SlStd.isClosedImmersion_weightTorus`), which is the property the pinned simply connected
Chevalley--Demazure group of type `A_r` is asked for and which the adjoint carrier does not have.

The whole ambient Lie algebra used is Mathlib's `LieAlgebra.SpecialLinear.sl`, and the Kostant form
depends only on the numbered generators above, so every carrier below traces back to explicit
matrices; no existence or classification theorem is invoked anywhere.

This file works over `ℤ` and proves neither reductivity, maximality of the torus, nor an
identification with the special linear group scheme. Those are proved over fields in the modules
built on it: `TauCeti.SlStd.reductiveCommHopfAlgProperty_finiteTypeSpecialization` (reductive over
every algebraically closed field),
`TauCeti.SlStd.eq_range_weightTorusPoints_of_le_of_isMulCommutative` (the weight torus is maximal
among commutative subgroups of the points over an infinite field) and
`TauCeti.SlStd.baseChangeDefiningIdeal_eq_specialLinearDefiningHopfIdeal` (the carrier is
scheme-theoretically `SL_{r+1}` over an algebraically closed field). No group here is claimed to be
finite or simple.

## Main definitions

* `TauCeti.SlStd.rootGenerator` and `TauCeti.SlStd.cartanGenerator`: the Bourbaki-numbered
  Chevalley generators of `sl_{r+1}`, as elements of `LieAlgebra.SpecialLinear.sl`.
* `TauCeti.SlStd.rep`: the standard representation, extended to the universal enveloping algebra.
* `TauCeti.SlStd.weight` and `TauCeti.SlStd.rootGeneratorWeight`: the integral weights of the
  coordinate vectors and the roots of the numbered generators.
* `TauCeti.SlStd.lattice` and `TauCeti.SlStd.latticeBasis`: the standard admissible lattice and its
  coordinate basis.
* `TauCeti.SlStd.definingIdeal` and `TauCeti.SlStd.definingIdeal_def`: the Hopf ideal cutting the
  carrier out of the coordinate Hopf algebra of `GL_{r+1}`, in terms of which
  `TauCeti.SlStd.points_def` presents its points, together with its characterization as the
  generic Kostant toral defining ideal.
* `TauCeti.SlStd.groupScheme`, `TauCeti.SlStd.carrierι`, `TauCeti.SlStd.rootSubgroup`,
  `TauCeti.SlStd.weightTorus`, `TauCeti.SlStd.points`, `TauCeti.SlStd.rootSubgroupPoints`, and
  `TauCeti.SlStd.weightTorusPoints`: the carrier, its closed immersion into `GL_{r+1}`, its pinned
  generating morphisms, its matrix points, and the parametrized root subgroups and split torus
  inside those points.

## Main results

* `TauCeti.SlStd.lie_cartanGenerator_rootGenerator`: the numbered Cartan generators act on the
  numbered root generators through the type `A_r` Cartan matrix.
* `TauCeti.SlStd.isSl2Triple_rootGenerator`: the numbered generators at a Bourbaki node form an
  `sl₂` triple, from the identification of them with matrix units of `sl_{r+1}`.
* `TauCeti.SlStd.isSl2Triple_rep_rootGenerator`: the numbered generators at a Bourbaki node form
  an `sl₂` triple in the standard representation.
* `TauCeti.SlStd.rep_kostantForm_mem_lattice`: the Kostant `ℤ`-form preserves the standard lattice,
  so the lattice is admissible.
* `TauCeti.SlStd.span_range_weight_eq_top`: the weights of the standard module generate the full
  character lattice.
* `TauCeti.SlStd.isClosedImmersion_rootSubgroup` and
  `TauCeti.SlStd.isClosedImmersion_weightTorus`: the root subgroups and the split torus are closed
  subgroups of the carrier.
* `TauCeti.SlStd.torusPoints_conj_rootSubgroupParam` and
  `TauCeti.SlStd.weightTorus_conj_rootSubgroup`: the pinning equation
  `t(s) x_k(u) t(s)⁻¹ = x_k(α_k(s) u)`, in the linear automorphisms of the base-changed lattice
  `A ⊗[ℤ] lattice r` and on `A`-valued scheme points after corestriction to the carrier.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §27, and
  *Linear Algebraic Groups*, §§26--27, for admissible lattices and the weights that distinguish
  the simply connected form from the adjoint one.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I, for the numbering of the type
  `A` diagram and the index `r + 1` of the root lattice in the weight lattice.
-/

public section

namespace TauCeti.SlStd

universe v

open LieAlgebra.SpecialLinear
open scoped Matrix TensorProduct
open scoped CategoryTheory.MonObj

variable (r : ℕ)

/-- The target coordinate of the numbered raising or lowering generator. -/
def rootTarget : Fin r ⊕ Fin r → Fin (r + 1)
  | .inl i => i.castSucc
  | .inr i => i.succ

/-- The source coordinate of the numbered raising or lowering generator. -/
def rootSource : Fin r ⊕ Fin r → Fin (r + 1)
  | .inl i => i.succ
  | .inr i => i.castSucc

@[simp] theorem rootTarget_inl (i : Fin r) : rootTarget r (.inl i) = i.castSucc := (rfl)
@[simp] theorem rootTarget_inr (i : Fin r) : rootTarget r (.inr i) = i.succ := (rfl)
@[simp] theorem rootSource_inl (i : Fin r) : rootSource r (.inl i) = i.succ := (rfl)
@[simp] theorem rootSource_inr (i : Fin r) : rootSource r (.inr i) = i.castSucc := (rfl)

/-- A numbered root generator moves between two distinct coordinates. -/
theorem rootTarget_ne_rootSource (k : Fin r ⊕ Fin r) : rootTarget r k ≠ rootSource r k := by
  cases k with
  | inl i => exact (Fin.castSucc_lt_succ (i := i)).ne
  | inr i => exact (Fin.castSucc_lt_succ (i := i)).ne'

/-- The two coordinates of a numbered root generator are adjacent, so their indices have odd
sum. -/
theorem odd_rootTarget_add_rootSource (k : Fin r ⊕ Fin r) :
    Odd ((rootTarget r k : ℕ) + (rootSource r k : ℕ)) := by
  cases k <;> simp

/-! ## The pinned Chevalley generators -/

/-- The Bourbaki-numbered raising and lowering generators of `sl_{r+1}`: the matrix unit
`E_{i, i+1}` at `Sum.inl i` and `E_{i+1, i}` at `Sum.inr i`. -/
def rootGenerator (k : Fin r ⊕ Fin r) : sl (Fin (r + 1)) ℚ :=
  single (rootTarget r k) (rootSource r k) (rootTarget_ne_rootSource r k) 1

/-- The Bourbaki-numbered Cartan generators of `sl_{r+1}`: the diagonal matrix
`E_{i,i} - E_{i+1,i+1}`. -/
def cartanGenerator (i : Fin r) : sl (Fin (r + 1)) ℚ :=
  singleSubSingle i.castSucc i.succ 1

@[simp]
theorem val_rootGenerator (k : Fin r ⊕ Fin r) :
    (rootGenerator r k : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ) =
      Matrix.single (rootTarget r k) (rootSource r k) 1 := (rfl)

@[simp]
theorem val_cartanGenerator (i : Fin r) :
    (cartanGenerator r i : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ) =
      Matrix.single i.castSucc i.castSucc 1 - Matrix.single i.succ i.succ 1 := (rfl)

/-- **The numbered Chevalley generators at a Bourbaki node form an `sl₂` triple** in `sl_{r+1}`:
they are the matrix units `E_{i, i+1}`, `E_{i+1, i}` and the diagonal difference
`E_{i,i} - E_{i+1,i+1}`. -/
theorem isSl2Triple_rootGenerator (i : Fin r) :
    _root_.IsSl2Triple (cartanGenerator r i) (rootGenerator r (.inl i))
      (rootGenerator r (.inr i)) := by
  simpa only [rootGenerator, cartanGenerator, rootTarget, rootSource] using
    isSl2Triple_single (Fin.castSucc_lt_succ (i := i)).ne

/-! ## The standard representation -/

/-- The standard representation of `sl_{r+1}` on coordinate vectors, extended to the universal
enveloping algebra. -/
noncomputable def rep :
    _root_.UniversalEnvelopingAlgebra ℚ (sl (Fin (r + 1)) ℚ) →ₐ[ℚ]
      Module.End ℚ (Fin (r + 1) → ℚ) :=
  LieSubalgebra.matrixRepresentation (sl (Fin (r + 1)) ℚ)

theorem rep_ι_apply (x : sl (Fin (r + 1)) ℚ) (v : Fin (r + 1) → ℚ) :
    rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v =
      (x : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ) *ᵥ v :=
  LieSubalgebra.matrixRepresentation_ι_apply _ x v

/-- A numbered root generator reads off one coordinate and writes it into another. -/
theorem rep_rootGenerator_apply (k : Fin r ⊕ Fin r) (v : Fin (r + 1) → ℚ) :
    rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k)) v =
      v (rootSource r k) • Pi.single (rootTarget r k) 1 := by
  rw [rep_ι_apply, val_rootGenerator, Matrix.single_mulVec_eq, one_mul]

/-- A numbered root generator sends the coordinate vector at its source to the one at its
target. -/
theorem rep_rootGenerator_single_source (k : Fin r ⊕ Fin r) :
    rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k))
        (Pi.single (rootSource r k) 1) = Pi.single (rootTarget r k) 1 := by
  rw [rep_rootGenerator_apply, Pi.single_eq_same, one_smul]

/-- Applying a numbered root generator twice to a vector gives zero: it writes into a coordinate
it does not read from. -/
theorem rep_rootGenerator_rep_rootGenerator_eq_zero (k : Fin r ⊕ Fin r) (v : Fin (r + 1) → ℚ) :
    rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k))
        (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k)) v) = 0 := by
  rw [rep_rootGenerator_apply r k v, map_smul, rep_rootGenerator_apply,
    Pi.single_eq_of_ne (rootTarget_ne_rootSource r k).symm 1, zero_smul, smul_zero]

/-- **Every numbered root generator squares to zero in the standard representation.** -/
theorem pow_two_rep_rootGenerator_eq_zero (k : Fin r ⊕ Fin r) :
    rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k)) ^ 2 = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [pow_two, Module.End.mul_apply, rep_rootGenerator_rep_rootGenerator_eq_zero,
    LinearMap.zero_apply]

/-- Every numbered root generator acts nilpotently. -/
theorem isNilpotent_rep_rootGenerator (k : Fin r ⊕ Fin r) :
    IsNilpotent (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k))) :=
  ⟨2, pow_two_rep_rootGenerator_eq_zero r k⟩

/-- Every numbered root generator has nilpotency class exactly two in the standard
representation. -/
theorem nilpotencyClass_rep_rootGenerator (k : Fin r ⊕ Fin r) :
    nilpotencyClass
        (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k))) = 2 := by
  refine nilpotencyClass_eq_succ_iff.mpr ⟨pow_two_rep_rootGenerator_eq_zero r k, ?_⟩
  rw [pow_one]
  intro hzero
  have h := DFunLike.congr_fun hzero (Pi.single (rootSource r k) 1)
  rw [rep_rootGenerator_single_source] at h
  have := congrFun h (rootTarget r k)
  simp at this

/-! ## Weights and roots -/

/-- The integral weight of the `k`-th standard coordinate vector on the numbered Cartan
generators. These are the weights `ε₀, …, ε_r` of the standard module, written in the basis of
fundamental weights. -/
def weight (k : Fin (r + 1)) (i : Fin r) : ℤ :=
  (if k = i.castSucc then 1 else 0) - (if k = i.succ then 1 else 0)

/-- The standard-module weight in Kronecker-delta form. -/
@[simp]
theorem weight_def (k : Fin (r + 1)) (i : Fin r) :
    weight r k i =
      (if k = i.castSucc then 1 else 0) - (if k = i.succ then 1 else 0) :=
  by rw [weight]

/-- A standard-module weight as the difference of its possible adjacent basis characters. -/
theorem weight_eq_dite_single_sub_dite_single (k : Fin (r + 1)) :
    weight r k =
      (if hk : (k : ℕ) < r then Pi.single ⟨k, hk⟩ 1 else 0) -
        (if hk : 0 < (k : ℕ) then Pi.single ⟨k - 1, by omega⟩ 1 else 0) := by
  funext i
  simp only [weight_def, Pi.sub_apply]
  split_ifs
  all_goals simp only [Pi.single_apply, Pi.zero_apply]
  all_goals try split_ifs
  all_goals simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
  all_goals omega

/-- The weights of the standard representation of `sl_{r+1}` are pairwise distinct. -/
theorem weight_injective : Function.Injective (weight r) := by
  intro k l hkl
  by_contra hne
  have aux {a b : Fin (r + 1)} (hab : (a : ℕ) < b)
      (hweight : weight r a = weight r b) : False := by
    have ha : (a : ℕ) < r := by omega
    let i : Fin r := ⟨a, ha⟩
    have hvalue := congrFun hweight i
    simp only [weight_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hvalue
    dsimp only [i] at hvalue
    split_ifs at hvalue <;> omega
  have hval : (k : ℕ) ≠ l := fun h ↦ hne (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact aux hlt hkl
  · exact aux hgt hkl.symm

/-- The weights of the standard representation sum to zero. -/
theorem sum_weight_eq_zero : ∑ k, weight r k = 0 := by
  funext i
  simp [weight]

/-- The root of a numbered raising or lowering generator, as an integral character of the
numbered Cartan generators: the `i`-th row of the type `A` Cartan matrix on a raising generator
and its negative on a lowering one. -/
def rootGeneratorWeight : Fin r ⊕ Fin r → Fin r → ℤ
  | .inl i => fun j => CartanMatrix.A r i j
  | .inr i => fun j => -CartanMatrix.A r i j

@[simp] theorem rootGeneratorWeight_inl (i j : Fin r) :
    rootGeneratorWeight r (.inl i) j = CartanMatrix.A r i j := (rfl)

@[simp] theorem rootGeneratorWeight_inr (i j : Fin r) :
    rootGeneratorWeight r (.inr i) j = -CartanMatrix.A r i j := (rfl)

/-- Every standard coordinate vector is a Cartan weight vector, of the weight recorded by
`TauCeti.SlStd.weight`. -/
theorem isCartanWeightVector_single (k : Fin (r + 1)) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector (cartanGenerator r) (rep r)
      (weight r k) (Pi.single k 1) := by
  refine (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff
    (cartanGenerator r) (rep r)).mpr fun j => ?_
  rw [rep_ι_apply, val_cartanGenerator, ← Matrix.diagonal_single, ← Matrix.diagonal_single,
    Matrix.sub_mulVec, Matrix.diagonal_mulVec_single, Matrix.diagonal_mulVec_single,
    ← Pi.single_sub, ← Pi.single_smul']
  simp [weight, Pi.single_apply]

/-- The Kronecker coefficient produced by bracketing a numbered Cartan generator with a numbered
root generator is the corresponding entry of the type `A` Cartan matrix, with a sign for the
lowering generators. -/
private theorem ite_sub_ite_sub_ite_sub_ite_eq_rootGeneratorWeight (k : Fin r ⊕ Fin r)
    (j : Fin r) :
    ((if j.castSucc = rootTarget r k then (1 : ℤ) else 0) -
        (if j.succ = rootTarget r k then 1 else 0)) -
      ((if rootSource r k = j.castSucc then (1 : ℤ) else 0) -
        (if rootSource r k = j.succ then 1 else 0)) = rootGeneratorWeight r k j := by
  cases k with
  | inl i =>
      rw [rootTarget_inl, rootSource_inl, rootGeneratorWeight_inl, CartanMatrix.A]
      simp only [Matrix.of_apply, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
      split_ifs <;> omega
  | inr i =>
      rw [rootTarget_inr, rootSource_inr, rootGeneratorWeight_inr, CartanMatrix.A]
      simp only [Matrix.of_apply, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
      split_ifs <;> omega

/-- **The numbered Cartan generators act on the numbered root generators through the type `A`
Cartan matrix.** This is the relation that makes the split torus of the carrier below act on the
root subgroup at `k` through the character `TauCeti.SlStd.rootGeneratorWeight r k`. -/
theorem lie_cartanGenerator_rootGenerator (k : Fin r ⊕ Fin r) (j : Fin r) :
    ⁅cartanGenerator r j, rootGenerator r k⁆ =
      ((rootGeneratorWeight r k j : ℤ) : ℚ) • rootGenerator r k := by
  let _ : LieRing (Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ) := LieRing.ofAssociativeRing
  refine Subtype.ext ?_
  have hcoe : (((((rootGeneratorWeight r k j : ℤ) : ℚ) • rootGenerator r k) :
      sl (Fin (r + 1)) ℚ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ) =
      ((rootGeneratorWeight r k j : ℤ) : ℚ) •
        Matrix.single (rootTarget r k) (rootSource r k) (1 : ℚ) := by
    rw [SetLike.val_smul, val_rootGenerator]
  rw [LieSubalgebra.coe_bracket, hcoe]
  rw [val_cartanGenerator, val_rootGenerator,
    lie_single_of_mem_diagonalCartan
      (sub_mem (single_self_mem_diagonalCartan j.castSucc 1)
        (single_self_mem_diagonalCartan j.succ 1)),
    ← ite_sub_ite_sub_ite_sub_ite_eq_rootGeneratorWeight r k j]
  simp only [Matrix.sub_apply, Matrix.single_apply, and_self, Int.cast_sub,
    apply_ite (fun z : ℤ => (z : ℚ)), Int.cast_one, Int.cast_zero, eq_comm]

/-! ## The standard admissible lattice -/

/-- **The standard `ℤ`-lattice of the standard `sl_{r+1}`-module**, spanned by the coordinate
vectors. -/
def lattice : Submodule ℤ (Fin (r + 1) → ℚ) :=
  TauCeti.coordinateLattice (Fin (r + 1))

/-- A vector lies in the standard lattice exactly when all of its coordinates are integers. -/
@[simp]
theorem mem_lattice_iff {v : Fin (r + 1) → ℚ} :
    v ∈ lattice r ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = v i := by
  exact TauCeti.mem_coordinateLattice_iff (Fin (r + 1))

theorem single_mem_lattice (i : Fin (r + 1)) : Pi.single i (1 : ℚ) ∈ lattice r := by
  rw [← Pi.basisFun_apply]
  exact TauCeti.basisFun_mem_coordinateLattice (Fin (r + 1)) i

/-- The coordinate basis of the standard lattice.

The carrier subtype and `ℤ`-module structure of a submodule are definitionally equal to those of
its underlying additive subgroup, so the restricted-scalars basis has the displayed target type. -/
noncomputable def latticeBasis : Module.Basis (Fin (r + 1)) ℤ (lattice r).toAddSubgroup :=
  TauCeti.coordinateLatticeBasis (Fin (r + 1))

@[simp]
theorem coe_latticeBasis (i : Fin (r + 1)) :
    ((latticeBasis r i : (lattice r).toAddSubgroup) : Fin (r + 1) → ℚ) = Pi.single i 1 := by
  rw [← Pi.basisFun_apply, latticeBasis]
  exact TauCeti.coe_coordinateLatticeBasis (Fin (r + 1)) i

/-! ## Stability of the lattice under the Kostant form -/

/-- A numbered root generator carries the standard lattice into itself. -/
theorem rep_rootGenerator_mem_lattice (k : Fin r ⊕ Fin r) {v : Fin (r + 1) → ℚ}
    (hv : v ∈ lattice r) :
    rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k)) v ∈ lattice r := by
  obtain ⟨z, hz⟩ := (mem_lattice_iff r).1 hv (rootSource r k)
  rw [rep_rootGenerator_apply, ← hz, Int.cast_smul_eq_zsmul]
  exact zsmul_mem (single_mem_lattice r _) z

/-- **The standard lattice is an admissible lattice**: the Kostant `ℤ`-form presented by the
numbered Chevalley generators preserves it. The root generators square to zero on the standard
module and preserve the lattice, and the coordinate vectors are weight vectors with integer
weights. -/
theorem rep_kostantForm_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ (sl (Fin (r + 1)) ℚ)}
    (hu : u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm (rootGenerator r)
      (cartanGenerator r))
    {v : Fin (r + 1) → ℚ} (hv : v ∈ lattice r) :
    rep r u v ∈ lattice r :=
  TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice (rootGenerator r)
    (cartanGenerator r) (rep r) (wt := weight r) (pow_two_rep_rootGenerator_eq_zero r)
    (fun k _ hw => rep_rootGenerator_mem_lattice r k hw) (isCartanWeightVector_single r) hu hv

/-! ## The weights generate the full character lattice -/

/-- **The weights of the standard module generate the full character lattice.** This is the
property that separates the standard module from the adjoint one, whose weights are the roots and
generate the root lattice, of index `r + 1`. It is what makes the rank-`r` split torus a closed
subgroup of the carrier assembled below. -/
theorem span_range_weight_eq_top : Submodule.span ℤ (Set.range (weight r)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun ℤ (Fin r)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  -- The `i`-th fundamental weight is `ε₀ + ⋯ + εᵢ`.
  have h : Pi.basisFun ℤ (Fin r) i = ∑ k ∈ Finset.Iic i.castSucc, weight r k := by
    funext j
    simp only [weight_def, Finset.sum_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_Iic, Pi.basisFun_apply, Pi.single_apply, Fin.castSucc_le_castSucc_iff,
      Fin.succ_le_castSucc_iff]
    split_ifs <;> omega
  exact h ▸ Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨k, rfl⟩

/-! ## The pinned carrier of type `A_r` -/

section Carrier

open AlgebraicGeometry CategoryTheory

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

attribute [local instance 100] LieRing.ofAssociativeRing in
/-- The standard representation carries the numbered `sl₂` triple at node `i` to an `sl₂` triple
of endomorphisms of the standard module. -/
theorem isSl2Triple_rep_rootGenerator (i : Fin r) :
    _root_.IsSl2Triple (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (cartanGenerator r i)))
      (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r (.inl i))))
      (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r (.inr i)))) := by
  refine (isSl2Triple_rootGenerator r i).map
    ((rep r).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)) fun hzero => ?_
  have h := congrFun (DFunLike.congr_fun hzero (Pi.single i.castSucc 1)) i.castSucc
  simp only [LieHom.comp_apply, AlgHom.toLieHom_apply, rep_ι_apply, val_cartanGenerator,
    LinearMap.zero_apply, Pi.zero_apply] at h
  simp [(Fin.castSucc_lt_succ (i := i)).ne'] at h

/-- Every coordinate basis vector of the standard lattice is a Cartan weight vector. -/
theorem isCartanWeightVector_latticeBasis (k : Fin (r + 1)) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector (cartanGenerator r) (rep r)
      (weight r k)
      ((latticeBasis r k : (lattice r).toAddSubgroup) : Fin (r + 1) → ℚ) := by
  rw [coe_latticeBasis]
  exact isCartanWeightVector_single r k

/-- The Hopf ideal cutting the type `A_r` carrier out of the coordinate Hopf algebra of
`GL_{r+1}` over `ℤ`.

Like `TauCeti.SlStd.groupScheme` below, and like the generic
`TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme` it is cut out of, this is an
`abbrev`: the descent arguments of
`TauCeti/Algebra/Lie/SpecialLinear/StandardCarrier/GraphAutomorphism.lean` feed it straight into
the generic Kostant comap lemmas and the generic toral coordinate maps, which are stated for the
ideal it names. Consumers that only need to know which ideal this is should rewrite with
`TauCeti.SlStd.definingIdeal_def` rather than unfold it. -/
noncomputable abbrev definingIdeal :
    HopfIdeal ℤ (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r)

/-- The defining ideal is the one supplied by the generic Kostant toral-closure construction. -/
theorem definingIdeal_def :
    definingIdeal r =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) := by
  rw [definingIdeal]

/-- **The full-weight Chevalley carrier of type `A_r`**: the smallest closed subgroup scheme of
`GL_{r+1}` over `ℤ` containing the divided-power exponential root subgroups of the numbered
Chevalley generators of `sl_{r+1}` and the weight torus of the standard lattice. -/
noncomputable abbrev groupScheme : Grp (Over (Spec (CommRingCat.of ℤ))) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r)

/-- **The canonical closed immersion of the type `A_r` carrier into `GL_{r+1}`**: the carrier is
by construction a closed subgroup scheme of the general linear group scheme of the standard
lattice. -/
noncomputable def carrierι : groupScheme r ⟶ TauCeti.GeneralLinear.groupScheme ℤ (r + 1) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r)

/-- The ambient inclusion of the type `A_r` carrier is the inclusion supplied by the generic
Kostant toral-closure construction. -/
theorem carrierι_def :
    carrierι r =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) := by
  rw [carrierι]

/-- **The type `A_r` carrier is a closed subgroup scheme of `GL_{r+1}`.** -/
instance isClosedImmersion_carrierι : IsClosedImmersion (carrierι r).hom.hom.left := by
  rw [carrierι]
  infer_instance

/-- The numbered root subgroup `x_k : 𝔾ₐ → G` of the type `A_r` carrier. -/
noncomputable def rootSubgroup (k : Fin r ⊕ Fin r) :
    AdditiveGroup.groupScheme ℤ ⟶ groupScheme r :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) k

/-- The root subgroup is the one supplied by the generic Kostant toral-closure construction. -/
theorem rootSubgroup_def (k : Fin r ⊕ Fin r) :
    rootSubgroup r k =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) k := by
  rw [rootSubgroup]

/-- The rank-`r` split weight torus `T → G` of the type `A_r` carrier. Its maximality over an
infinite field is `TauCeti.SlStd.eq_range_weightTorusPoints_of_le_of_isMulCommutative`. -/
noncomputable def weightTorus : SplitTorus.groupScheme ℤ (Fin r) ⟶ groupScheme r :=
  TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r)

/-- The weight torus is the one supplied by the generic Kostant toral-closure construction. -/
theorem weightTorus_def :
    weightTorus r =
      TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) := by
  rw [weightTorus]

/-- Including a numbered root subgroup of the type `A_r` carrier into `GL_{r+1}` recovers the
Kostant root subgroup of the numbered generator. -/
@[simp]
theorem rootSubgroup_comp_carrierι (k : Fin r ⊕ Fin r) :
    rootSubgroup r k ≫ carrierι r =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroup (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
        (isNilpotent_rep_rootGenerator r k) (latticeBasis r) := by
  rw [rootSubgroup, carrierι,
    TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral_comp_ι]

/-- Including the split torus of the type `A_r` carrier into `GL_{r+1}` recovers the weight torus
of the weights of the standard module. -/
@[simp]
theorem weightTorus_comp_carrierι :
    weightTorus r ≫ carrierι r = TauCeti.GeneralLinear.weightTorus (R := ℤ) (weight r) := by
  rw [weightTorus, carrierι,
    TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral_comp_ι]

/-- The `A`-valued points of the type `A_r` carrier, as matrices. -/
noncomputable def points (A : Type v) [CommRing A] :
    Subgroup (Matrix.GeneralLinearGroup (Fin (r + 1)) A) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A

/-- The points of the type `A_r` carrier are the invertible matrices cut out by its defining Hopf
ideal. This is the presentation the functoriality of the points is read off. -/
theorem points_def (A : Type v) [CommRing A] :
    points r A =
      TauCeti.GeneralLinear.hopfIdealPointsSubgroup (r + 1) (definingIdeal r) A := by
  rw [points, definingIdeal]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup_def
    _ _ _ _ _ _ _ _ A

/-- **The parametrized numbered root subgroup inside the type-`A_r` carrier points.** The
parameter is read through the canonical multiplicative copy of the additive group of `A`. -/
noncomputable def rootSubgroupPoints (i : Fin r ⊕ Fin r) (A : Type v) [CommRing A] :
    Multiplicative A →* points r A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralRootSubgroupPoints
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) i A

/-- The numbered root subgroup point is the corresponding divided-power exponential matrix. -/
@[simp]
theorem coe_rootSubgroupPoints (i : Fin r ⊕ Fin r) (A : Type v) [CommRing A]
    (u : Multiplicative A) :
    (rootSubgroupPoints r i A u : Matrix.GeneralLinearGroup (Fin (r + 1)) A) =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) i
        (isNilpotent_rep_rootGenerator r i) (latticeBasis r)
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u) := by
  exact TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints
    _ _ _ _ _ _ _ _ i A u

/-- **The split weight torus inside the type-`A_r` carrier points.** -/
noncomputable def weightTorusPoints (A : Type v) [CommRing A] :
    (Fin r → Aˣ) →* points r A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralWeightTorusPoints
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A

/-- A split-torus point is the diagonal matrix whose entries are its values on the standard-module
weights. -/
@[simp]
theorem coe_weightTorusPoints (A : Type v) [CommRing A] (s : Fin r → Aˣ) :
    (weightTorusPoints r A s : Matrix.GeneralLinearGroup (Fin (r + 1)) A) =
      TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix
        (lattice r).toAddSubgroup (latticeBasis r) (weight r) s := by
  exact TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralWeightTorusPoints
    _ _ _ _ _ _ _ _ A s

/-- A matrix is a point of the type `A_r` carrier exactly when the associated convolution point
kills its toral defining Hopf ideal. -/
-- Not `@[simp]`: rewriting membership into this raw condition defeats the membership lemmas.
theorem mem_points_iff (A : Type v) [CommRing A]
    (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
    g ∈ points r A ↔
      ∀ x ∈ TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal (rootGenerator r)
          (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
          (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
          (isNilpotent_rep_rootGenerator r)
          (latticeBasis r) (weight r),
        ((GeneralLinear.pointsMulEquiv (R := ℤ) (r + 1)).symm g).ofConv x = 0 := by
  rw [points]
  exact TauCeti.UniversalEnvelopingAlgebra.mem_kostantToralPointsSubgroup_iff
    _ _ _ _ _ _ _ _ A g

/-! ## The pinning -/

/-- A numbered root generator sends its source lattice vector to its target lattice vector and
annihilates every other lattice basis vector. -/
theorem rep_rootGenerator_latticeBasis_apply (k : Fin r ⊕ Fin r) (s : Fin (r + 1)) :
    rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k))
        ((latticeBasis r s : (lattice r).toAddSubgroup) : Fin (r + 1) → ℚ) =
      if s = rootSource r k then
        ((latticeBasis r (rootTarget r k) : (lattice r).toAddSubgroup) : Fin (r + 1) → ℚ)
      else 0 := by
  rw [coe_latticeBasis, rep_rootGenerator_apply]
  split_ifs with hs
  · subst hs
    rw [Pi.single_eq_same, one_smul, coe_latticeBasis]
  · simp [hs]

/-- A numbered root generator carries the coordinate basis vector at its source to the one at its
target. This is the root step that makes the root subgroup a closed copy of `𝔾ₐ`. -/
private theorem rep_rootGenerator_latticeBasis (k : Fin r ⊕ Fin r) :
    rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k))
        ((latticeBasis r (rootSource r k) : (lattice r).toAddSubgroup) : Fin (r + 1) → ℚ) =
      (1 : ℤ) • ((latticeBasis r (rootTarget r k) : (lattice r).toAddSubgroup) :
        Fin (r + 1) → ℚ) := by
  rw [rep_rootGenerator_latticeBasis_apply, ite_eq_left rfl, one_smul]

/-- **The coordinate morphism of every numbered root subgroup of the type `A_r` carrier is
surjective.** -/
theorem rootSubgroupCoordinateMap_surjective (k : Fin r ⊕ Fin r) :
    Function.Surjective
      (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) k).hom :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap_surjective
    _ _ _ _ _ k _ _ _ isUnit_one (rep_rootGenerator_latticeBasis r k)
    (rep_rootGenerator_rep_rootGenerator_eq_zero r k _)

/-- **Every numbered root subgroup of the type `A_r` carrier is a closed immersion.** -/
instance isClosedImmersion_rootSubgroup (k : Fin r ⊕ Fin r) :
    IsClosedImmersion (rootSubgroup r k).hom.hom.left := by
  rw [rootSubgroup]
  exact TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantRootSubgroupToToral
    _ _ _ _ _ k _ _ _ isUnit_one (rep_rootGenerator_latticeBasis r k)
    (rep_rootGenerator_rep_rootGenerator_eq_zero r k _)

/-- **The split torus of the type `A_r` carrier is a closed immersion.** This is exactly where the
full-weight property is used: the weights of the standard module generate the whole character
lattice, so the rank-`r` split torus embeds rather than mapping onto a proper quotient. -/
instance isClosedImmersion_weightTorus :
    IsClosedImmersion (weightTorus r).hom.hom.left :=
  TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantWeightTorusToToral _ _ _ _ _ _ _ _
    (span_range_weight_eq_top r)

/-- The parametrized numbered root subgroup on points of a value algebra. -/
noncomputable def rootSubgroupParam (k : Fin r ⊕ Fin r) (A : CommAlgCat ℤ) :
    Multiplicative A →* LinearMap.GeneralLinearGroup A (A ⊗[ℤ] (lattice r).toAddSubgroup) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupParam (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
    (isNilpotent_rep_rootGenerator r k) A

/-- The split weight torus on points of a value algebra. -/
noncomputable def torusPoints (A : CommAlgCat ℤ) :
    (Fin r → Aˣ) →* LinearMap.GeneralLinearGroup A (A ⊗[ℤ] (lattice r).toAddSubgroup) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints (lattice r).toAddSubgroup
    (latticeBasis r) (weight r) A

/-- **The pinning equation on the base-changed lattice.** In the linear automorphisms of
`A ⊗[ℤ] lattice r`, a torus point `s` conjugates the root-subgroup element of parameter `u` into the
one of parameter `α_k(s) u`, where `α_k` is the `k`-th row of the type `A_r` Cartan matrix on a
raising generator and its negative on a lowering one. -/
theorem torusPoints_conj_rootSubgroupParam (k : Fin r ⊕ Fin r) (A : CommAlgCat ℤ)
    (s : Fin r → Aˣ) (u : Multiplicative A) :
    torusPoints r A s * rootSubgroupParam r k A u * (torusPoints r A s)⁻¹ =
      rootSubgroupParam r k A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s (rootGeneratorWeight r k) : A) *
            Multiplicative.toAdd u)) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints_conj_kostantRootSubgroupParam
    _ _ _ _ _ _ _ (isCartanWeightVector_latticeBasis r)
    (fun j => lie_cartanGenerator_rootGenerator r k j) _ A s u

/-- **The pinning equation on `A`-valued scheme points of the type `A_r` carrier.** After
corestriction to the carrier, conjugation by a split-torus point rescales the parameter of a
numbered root subgroup by the corresponding root character. -/
theorem weightTorus_conj_rootSubgroup (k : Fin r ⊕ Fin r) (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin r)).X)
    (u : A) :
    (s ≫ (weightTorus r).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫
          (rootSubgroup r k).hom.hom) *
        (s ≫ (weightTorus r).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (rootGeneratorWeight r k) : A) * u)) ≫
        (rootSubgroup r k).hom.hom :=
  TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral_conj_kostantRootSubgroupToToralParam
    _ _ _ _ _ _ _ (isCartanWeightVector_latticeBasis r) (isNilpotent_rep_rootGenerator r) A
    (fun j => lie_cartanGenerator_rootGenerator r k j) s u

end Carrier

end TauCeti.SlStd
