/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Casimir
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.LeftRegular
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Basic

import TauCeti.LinearAlgebra.CliffordAlgebra.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Coordinates

/-!
# The Casimir element in the Clifford algebra of the Killing form

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form `κ`, and let
`q = CliffordAlgebra.adjointCliffordHom K L` be the quadratic lift of its adjoint representation to
the Clifford algebra of the quadratic form `x ↦ κ(x, x)`. For a basis `b` of `L` with Killing-dual
basis `b'`, this file proves

`∑ i, q (b i) * q (b' i) = dim L / 8`

in the Clifford algebra. Consequently the Casimir element of `U(L)` acts on Kostant's left-regular
module by the scalar `dim L / 8`, on every vector. Every highest weight `μ` occurring in that module
therefore satisfies the single quadratic equation `⟨μ + ρ, μ + ρ⟩ - ⟨ρ, ρ⟩ = dim L / 8`. This is the
constraint behind Kostant's isotypy theorem, in which the half-sum `ρ` of the positive roots is the
only highest weight of the module.

The value of the scalar comes from the trace form of the lift: the scalar part of `q x * q y` is
`κ(x, y) / 8`.

## Main results

* `CliffordAlgebra.scalarTrace_adjointCliffordHom`: the scalar part of `q x` vanishes.
* `CliffordAlgebra.scalarTrace_adjointCliffordHom_mul_adjointCliffordHom`: the scalar part of
  `q x * q y` is `κ(x, y) / 8`.
* `CliffordAlgebra.sum_adjointCliffordHom_mul_adjointCliffordHom_killingDualBasis`: the image of
  the Casimir element under the lift is the scalar `dim L / 8`.
* `CliffordAlgebra.representation_casimirElement_kostant_apply`: the Casimir element acts on
  Kostant's module by that scalar.
* `CliffordAlgebra.casimirScalar_eq_of_isHighestWeightVector_kostant`: the Casimir scalar of a
  highest weight occurring in Kostant's module is `dim L / 8`.

## Implementation notes

The proof that the image of the Casimir element is central goes through Kostant's cubic element
`γ = ∑ i, ι (b i) * q (b' i)`, which commutes with the lift and satisfies
`ι x * γ + γ * ι x = 6 • q x`. These two relations show that `γ²` commutes with every generator,
and they express the image of the Casimir element as `γ² / 3`, which is why `3` is assumed
invertible in `K`.

## References

* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem*, Adv. Math. 125
  (1997), 275--350.
* B. Kostant, *A cubic Dirac operator and the emergence of Euler number multiplets of
  representations for equal rank subgroups*, Duke Math. J. 100 (1999), 447--501.
* E. Meinrenken, *Clifford Algebras and Lie Theory*, Springer Ergebnisse 58 (2013), Chapters
  5--10.
-/

public section

universe u v w

open TauCeti TauCeti.LieAlgebra
open scoped CliffordAlgebra

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [Invertible (2 : K)] [_root_.LieAlgebra.IsKilling K L]
  {ι' : Type w} [Fintype ι'] [DecidableEq ι']

variable (K) in
/-- The Clifford generator of a vector of `L`, for the Killing quadratic form. -/
private noncomputable abbrev gen (y : L) : CliffordAlgebra (killingQuadraticForm K L) :=
  ι (killingQuadraticForm K L) y

variable (K) in
/-- The quadratic lift of the adjoint representation, as a linear map. -/
private noncomputable abbrev adjLift : L →ₗ[K] CliffordAlgebra (killingQuadraticForm K L) :=
  (adjointCliffordHom K L : L →ₗ[K] CliffordAlgebra (killingQuadraticForm K L))

omit [FiniteDimensional K L] [LieRing L] [LieAlgebra K L] [_root_.LieAlgebra.IsKilling K L] in
/-- Four is nonzero in a field in which two is invertible. -/
private theorem four_ne_zero_of_invertible : (4 : K) ≠ 0 := by
  have h4 : (4 : K) = 2 * 2 := by norm_num
  rw [h4]
  exact mul_ne_zero (Invertible.ne_zero (2 : K)) (Invertible.ne_zero (2 : K))

omit [FiniteDimensional K L] [Invertible (2 : K)] [_root_.LieAlgebra.IsKilling K L] in
/-- The Clifford relation between a pair of generators and the Killing form. -/
private theorem gen_mul_gen_add_swap (a c : L) :
    gen K a * gen K c + gen K c * gen K a =
      (2 * killingForm K L a c) • (1 : CliffordAlgebra (killingQuadraticForm K L)) := by
  rw [gen, gen, ι_mul_ι_add_swap, polar_killingQuadraticForm, Algebra.algebraMap_eq_smul_one]

/-- The lift acts on a generator by the adjoint action, written as an equation of products. -/
private theorem adjLift_mul_gen (x y : L) :
    adjLift K x * gen K y = gen K y * adjLift K x + gen K ⁅x, y⁆ := by
  have h := kostant_lie_ι (K := K) x y
  rw [kostant_lie_def] at h
  rw [adjLift, LieHom.coe_toLinearMap, gen, gen, h, add_comm]

/-- Kostant's cubic element, along a basis and its Killing dual. -/
private noncomputable def cubic (b : Module.Basis ι' K L) :
    CliffordAlgebra (killingQuadraticForm K L) :=
  ∑ i, gen K (b i) * adjLift K (killingDualBasis b i)

/-- The cubic element anticommutes with a generator up to six times the lift. -/
private theorem gen_mul_cubic_add_cubic_mul_gen (b : Module.Basis ι' K L) (x : L) :
    gen K x * cubic b + cubic b * gen K x = (6 : K) • adjLift K x := by
  have hstep (i : ι') :
      gen K x * (gen K (b i) * adjLift K (killingDualBasis b i)) +
          gen K (b i) * adjLift K (killingDualBasis b i) * gen K x =
        (2 : K) • (killingForm K L x (b i) • adjLift K (killingDualBasis b i)) -
          gen K (b i) * gen K ⁅x, killingDualBasis b i⁆ := by
    have hgen := gen_mul_gen_add_swap (K := K) x (b i)
    have hneg : gen K ⁅killingDualBasis b i, x⁆ = -gen K ⁅x, killingDualBasis b i⁆ := by
      rw [← lie_skew, gen, gen, map_neg]
    have hexp : gen K x * (gen K (b i) * adjLift K (killingDualBasis b i)) +
        gen K (b i) * adjLift K (killingDualBasis b i) * gen K x =
        (gen K x * gen K (b i) + gen K (b i) * gen K x) * adjLift K (killingDualBasis b i) +
          gen K (b i) * (adjLift K (killingDualBasis b i) * gen K x -
            gen K x * adjLift K (killingDualBasis b i)) := by
      noncomm_ring
    rw [hexp, hgen, adjLift_mul_gen, hneg, smul_mul_assoc, one_mul, mul_smul]
    noncomm_ring
  have hlift : ∑ i, killingForm K L x (b i) • adjLift K (killingDualBasis b i) = adjLift K x := by
    simp only [← map_smul, ← map_sum, LinearMap.BilinForm.sum_apply_smul_dualBasis]
  have hmove := sum_apply_lie_killingDualBasis_add_eq_zero
    ((LinearMap.mul K _).compl₁₂ (ι (killingQuadraticForm K L)) (ι (killingQuadraticForm K L))) b x
  simp only [LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at hmove
  have hfour : (4 : K) • adjLift K x = _ := four_smul_adjointCliffordHom_eq_sum_ι_mul_ι b x
  rw [cubic, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  simp_rw [hstep]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hlift]
  simp only [gen]
  rw [eq_neg_of_add_eq_zero_right hmove, ← hfour, sub_neg_eq_add, ← add_smul]
  norm_num

/-- The cubic element commutes with the lift. -/
private theorem adjLift_mul_cubic (b : Module.Basis ι' K L) (x : L) :
    adjLift K x * cubic b = cubic b * adjLift K x := by
  have hmove := sum_apply_lie_killingDualBasis_add_eq_zero
    ((LinearMap.mul K _).compl₁₂ (ι (killingQuadraticForm K L)) (adjLift K)) b x
  simp only [LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at hmove
  rw [← sub_eq_zero, cubic, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  rw [← hmove, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hlie : adjLift K ⁅x, killingDualBasis b i⁆ =
      adjLift K x * adjLift K (killingDualBasis b i) -
        adjLift K (killingDualBasis b i) * adjLift K x := by
    simp only [adjLift, LieHom.coe_toLinearMap, LieHom.map_lie,
      LieRing.of_associative_ring_bracket]
  have hgen := adjLift_mul_gen (K := K) x (b i)
  have hgen' : ι (killingQuadraticForm K L) ⁅x, b i⁆ =
      adjLift K x * gen K (b i) - gen K (b i) * adjLift K x := by
    rw [hgen, gen]
    abel
  rw [hlie, hgen']
  simp only [gen]
  noncomm_ring

/-- The image of the Casimir element is a third of the square of the cubic element. -/
private theorem three_smul_sum_adjLift_mul_adjLift (b : Module.Basis ι' K L) :
    (3 : K) • ∑ i, adjLift K (b i) * adjLift K (killingDualBasis b i) = cubic b * cubic b := by
  have hleft : ∑ i, gen K (b i) * cubic b * adjLift K (killingDualBasis b i) =
      cubic b * cubic b := by
    calc
      _ = ∑ i, gen K (b i) * adjLift K (killingDualBasis b i) * cubic b :=
        Finset.sum_congr rfl fun i _ ↦ by rw [mul_assoc, ← adjLift_mul_cubic, mul_assoc]
      _ = cubic b * cubic b := by rw [← Finset.sum_mul, cubic]
  have hright : ∑ i, cubic b * gen K (b i) * adjLift K (killingDualBasis b i) =
      cubic b * cubic b := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, cubic]
  have hsix : (2 : K) • (3 : K) • ∑ i, adjLift K (b i) * adjLift K (killingDualBasis b i) =
      (2 : K) • (cubic b * cubic b) := by
    rw [smul_smul, Finset.smul_sum, two_smul]
    have h6 : (2 * 3 : K) = 6 := by norm_num
    simp_rw [h6, ← smul_mul_assoc, ← gen_mul_cubic_add_cubic_mul_gen b, add_mul]
    rw [Finset.sum_add_distrib, hleft, hright]
  exact smul_right_injective _ (Invertible.ne_zero (2 : K)) hsix

/-- The square of the cubic element commutes with every generator. -/
private theorem commute_cubic_mul_cubic_gen (b : Module.Basis ι' K L) (y : L) :
    Commute (cubic b * cubic b) (gen K y) := by
  have hanti := gen_mul_cubic_add_cubic_mul_gen b y
  have hcomm : (6 : K) • adjLift K y * cubic b = cubic b * (6 : K) • adjLift K y := by
    rw [smul_mul_assoc, mul_smul_comm, adjLift_mul_cubic]
  have hswap : cubic b * gen K y = (6 : K) • adjLift K y - gen K y * cubic b :=
    eq_sub_of_add_eq' hanti
  calc
    cubic b * cubic b * gen K y = cubic b * ((6 : K) • adjLift K y - gen K y * cubic b) := by
      rw [mul_assoc, hswap]
    _ = (6 : K) • adjLift K y * cubic b - cubic b * gen K y * cubic b := by
      rw [mul_sub, hcomm, mul_assoc]
    _ = (6 : K) • adjLift K y * cubic b -
        ((6 : K) • adjLift K y - gen K y * cubic b) * cubic b := by
      rw [hswap]
    _ = gen K y * (cubic b * cubic b) := by
      rw [sub_mul, mul_assoc]
      abel

/-- The image of the Casimir element under the lift lies in the even part. -/
private theorem sum_adjLift_mul_adjLift_mem_even (b : Module.Basis ι' K L) :
    ∑ i, adjLift K (b i) * adjLift K (killingDualBasis b i) ∈
      even (killingQuadraticForm K L) := by
  have hlift (x : L) : adjLift K x ∈ even (killingQuadraticForm K L) := by
    simpa only [adjLift, LieHom.coe_toLinearMap, adjointCliffordHom_apply] using
      (Subalgebra.mem_toSubmodule _).mp
        (quadraticLieSubalgebra_le_even _ (soEquivQuadratic _ _ _).property)
  exact sum_mem fun i _ ↦ mul_mem (hlift _) (hlift _)

omit [FiniteDimensional K L] [_root_.LieAlgebra.IsKilling K L] in
/-- The scalar part of a product of two generators is the Killing form. -/
private theorem scalarTrace_gen_mul_gen (a c : L) :
    scalarTrace (killingQuadraticForm K L) (gen K a * gen K c) = killingForm K L a c := by
  rw [gen, gen, scalarTrace_ι_mul_ι, associated_killingQuadraticForm]

/-- The scalar part of the quadratic lift of the adjoint representation vanishes. -/
theorem scalarTrace_adjointCliffordHom (x : L) :
    scalarTrace (killingQuadraticForm K L) (adjointCliffordHom K L x) = 0 := by
  have h := congrArg (scalarTrace (killingQuadraticForm K L))
    (four_smul_adjointCliffordHom_eq_sum_ι_mul_ι (Module.finBasis K L) x)
  simp_rw [map_sum, scalarTrace_gen_mul_gen, sum_killingForm_lie_killingDualBasis_eq_zero,
    map_smul, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left four_ne_zero_of_invertible

/-- The scalar part of a product of two generators and the lift is the invariant trilinear form. -/
private theorem two_mul_scalarTrace_gen_mul_gen_mul_adjLift (a c y : L) :
    2 * scalarTrace (killingQuadraticForm K L) (gen K a * gen K c * adjLift K y) =
      -killingForm K L a ⁅y, c⁆ := by
  have hsum : scalarTrace (killingQuadraticForm K L) (gen K a * gen K c * adjLift K y) +
      scalarTrace (killingQuadraticForm K L) (gen K c * gen K a * adjLift K y) = 0 := by
    rw [← map_add, ← add_mul, gen_mul_gen_add_swap, smul_mul_assoc, one_mul, map_smul]
    simp only [adjLift, LieHom.coe_toLinearMap, scalarTrace_adjointCliffordHom, smul_zero]
  have hdiff : scalarTrace (killingQuadraticForm K L) (gen K c * gen K a * adjLift K y) =
      scalarTrace (killingQuadraticForm K L) (gen K a * gen K c * adjLift K y) +
        killingForm K L a ⁅y, c⁆ := by
    rw [mul_assoc (gen K c), ← scalarTrace_mul_comm, mul_assoc, adjLift_mul_gen, mul_add, map_add,
      ← mul_assoc, scalarTrace_gen_mul_gen]
  rw [hdiff] at hsum
  linear_combination hsum

/-- **The trace form of the adjoint quadratic lift.** The scalar part of `q x * q y` is
`κ(x, y) / 8`, where `q` is the quadratic lift of the adjoint representation to the Clifford algebra
of the Killing form. -/
theorem scalarTrace_adjointCliffordHom_mul_adjointCliffordHom (x y : L) :
    scalarTrace (killingQuadraticForm K L) (adjointCliffordHom K L x * adjointCliffordHom K L y) =
      killingForm K L x y / 8 := by
  classical
  let b := Module.finBasis K L
  have hmul := congrArg
    (fun c ↦ scalarTrace (killingQuadraticForm K L) (c * adjLift K y))
    (four_smul_adjointCliffordHom_eq_sum_ι_mul_ι b x)
  simp only [smul_mul_assoc, map_smul, Finset.sum_mul, map_sum, smul_eq_mul] at hmul
  have hterm (i : Fin (Module.finrank K L)) :
      2 * scalarTrace (killingQuadraticForm K L)
          (gen K ⁅x, b i⁆ * gen K (killingDualBasis b i) * adjLift K y) =
        killingForm K L ⁅y, ⁅x, b i⁆⁆ (killingDualBasis b i) := by
    rw [two_mul_scalarTrace_gen_mul_gen_mul_adjLift,
      LieModule.traceForm_apply_lie_apply' K L L y ⁅x, b i⁆ (killingDualBasis b i)]
  have htrace : ∑ i, killingForm K L ⁅y, ⁅x, b i⁆⁆ (killingDualBasis b i) =
      killingForm K L x y := by
    have h := LinearMap.BilinForm.sum_apply_dualBasis_eq_trace
      (_root_.LieAlgebra.IsKilling.killingForm_nondegenerate K L) b
      ((_root_.LieAlgebra.ad K L y).comp (_root_.LieAlgebra.ad K L x))
    simp only [LinearMap.comp_apply, _root_.LieAlgebra.ad_apply] at h
    rw [Finset.sum_congr rfl fun i _ ↦ LieModule.traceForm_comm K L L ⁅y, ⁅x, b i⁆⁆ _, h,
      LieModule.traceForm_comm K L L x y]
    exact (LieModule.traceForm_apply_apply K L L y x).symm
  have height : (8 : K) ≠ 0 := by
    have h8 : (8 : K) = 4 * 2 := by norm_num
    rw [h8]
    exact mul_ne_zero four_ne_zero_of_invertible (Invertible.ne_zero (2 : K))
  rw [eq_div_iff height, ← htrace, Finset.sum_congr rfl fun i _ ↦ (hterm i).symm, ← Finset.mul_sum]
  simp only [adjLift, gen, LieHom.coe_toLinearMap] at hmul ⊢
  rw [← hmul]
  ring

/-- **The Casimir element under the adjoint quadratic lift is a scalar.** For a basis `b` of `L`
with Killing-dual basis `b'`, the sum `∑ i, q (b i) * q (b' i)` is the scalar `dim L / 8` in the
Clifford algebra of the Killing form. -/
theorem sum_adjointCliffordHom_mul_adjointCliffordHom_killingDualBasis [NeZero (3 : K)]
    (b : Module.Basis ι' K L) :
    ∑ i, adjointCliffordHom K L (b i) * adjointCliffordHom K L (killingDualBasis b i) =
      algebraMap K (CliffordAlgebra (killingQuadraticForm K L)) ((Module.finrank K L : K) / 8) := by
  have hcomm (y : L) :
      Commute (∑ i, adjLift K (b i) * adjLift K (killingDualBasis b i)) (gen K y) := by
    have h3 : ∑ i, adjLift K (b i) * adjLift K (killingDualBasis b i) =
        (3 : K)⁻¹ • (cubic b * cubic b) := by
      rw [← three_smul_sum_adjLift_mul_adjLift, smul_smul, inv_mul_cancel₀ (NeZero.ne _), one_smul]
    rw [h3]
    exact (commute_cubic_mul_cubic_gen b y).smul_left _
  obtain ⟨r, hr⟩ := exists_eq_algebraMap_of_mem_even_of_commute (killingQuadraticForm K L)
    (killingQuadraticForm_nondegenerate K L) _ (sum_adjLift_mul_adjLift_mem_even b) hcomm
  simp only [adjLift, LieHom.coe_toLinearMap] at hr
  have hvalue := congrArg (scalarTrace (killingQuadraticForm K L)) hr
  rw [map_sum, scalarTrace_algebraMap] at hvalue
  have hone (i : ι') : killingForm K L (b i) (killingDualBasis b i) = 1 := by
    rw [LieModule.traceForm_comm, LinearMap.BilinForm.apply_dualBasis_left, ite_eq_left rfl]
  simp only [scalarTrace_adjointCliffordHom_mul_adjointCliffordHom, hone, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hvalue
  rw [hr, ← hvalue, Module.finrank_eq_card_basis b, mul_one_div]

/-- **The Casimir element acts on Kostant's module by the scalar `dim L / 8`.** This holds on every
vector of the left-regular module, so every highest weight occurring in it satisfies the same
quadratic equation. -/
@[simp]
theorem representation_casimirElement_kostant_apply [NeZero (3 : K)]
    (c : CliffordAlgebra (killingQuadraticForm K L)) :
    UniversalEnvelopingAlgebra.representation K L (CliffordAlgebra (killingQuadraticForm K L))
        (casimirElement K L) c =
      ((Module.finrank K L : K) / 8) • c := by
  classical
  let b := Module.finBasis K L
  rw [casimirElement_eq_sum b, map_sum, LinearMap.sum_apply, Algebra.smul_def,
    ← sum_adjointCliffordHom_mul_adjointCliffordHom_killingDualBasis b, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, mul_apply_eq_comp, UniversalEnvelopingAlgebra.representation_ι,
    UniversalEnvelopingAlgebra.representation_ι, LieModule.toEnd_apply_apply,
    LieModule.toEnd_apply_apply, kostant_lie_def, kostant_lie_def, mul_assoc]

/-- **The quadratic equation for the highest weights of Kostant's module.** The Casimir scalar
`⟨μ + ρ, μ + ρ⟩ - ⟨ρ, ρ⟩` of any highest weight `μ` occurring in Kostant's module is `dim L / 8`. -/
theorem casimirScalar_eq_of_isHighestWeightVector_kostant [CharZero K]
    {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
    {base : (_root_.LieAlgebra.IsKilling.rootSystem H).Base} {μ : Module.Dual K H}
    {v : CliffordAlgebra (killingQuadraticForm K L)} (hv : IsHighestWeightVector base μ v) :
    casimirScalar base μ = (Module.finrank K L : K) / 8 := by
  have h := casimir_smul_of_isHighestWeightVector hv
  rw [representation_casimirElement_kostant_apply] at h
  exact smul_left_injective K hv.ne_zero h.symm

end CliffordAlgebra
