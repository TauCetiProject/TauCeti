/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
public import TauCeti.Analysis.Complex.RiemannSurface.Branch.EulerCharacteristic
public import TauCeti.Analysis.Complex.RiemannSurface.ChebyshevMap
public import TauCeti.Topology.CWComplex.Classical.Product
public import TauCeti.Topology.CWComplex.Classical.Sphere.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The branched-cover formula on polynomial maps of the Riemann sphere

This file checks the topological branched-cover formula
`χ(X) = deg f · χ(Y) - R(f)`
(`FiniteHolomorphicMap.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree`)
on polynomial maps of the Riemann sphere `OnePoint ℂ`, whose Euler characteristic is `2`.

The Riemann sphere punctured at `∞` and one finite point `c` is the punctured plane `ℂ \ {c}`,
which is homeomorphic to a circle times an open half-line. So it has finite CW type and Euler
characteristic `2 - 2 = 0`, one less for each puncture. This is the punctured target needed to
apply the branched-cover formula to a polynomial map whose finite branch values lie in `{c}`.

For `f = (z ↦ z²)`, of degree `2`, the local multiplicity is `2` at `0` and at `∞` and `1`
elsewhere, so `R(f) = 2`, and the branch values are `0` and `∞`. Puncturing at them gives the
punctured form `0 = 2 · 0` of the formula, whose preimage side is the same punctured sphere. The
branched-cover formula then reads `2 = 2 · 2 - 2`, and recovers `R(f) = 2` independently of the
local count. The Chebyshev map `z ↦ 4z(1 - z)`, with branch values `1` and `∞`, is a second
instance. The identity map has degree `1` and `R = 0`.

Finally, for every nonconstant polynomial `p` of degree `d`, counting the critical points of `p`
with multiplicity, together with the multiplicity `d` at `∞`, gives `R = 2d - 2`, so that both
sides of the branched-cover formula on `OnePoint ℂ` agree: `2 = d · 2 - (2d - 2)`.

## Main results

* `TauCeti.RiemannSurface.finiteCWType_compl_coe_pair_infty`: `OnePoint ℂ \ {c, ∞}` has finite
  CW type.
* `TauCeti.RiemannSurface.eulerChar_compl_coe_pair_infty`: its Euler characteristic is `0`.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.ramificationDegree_spherePolynomial`: a polynomial
  map of the sphere of degree `d ≥ 1` has ramification degree `2d - 2`.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.eulerChar_onePoint_eq_spherePolynomial`: the
  branched-cover formula for every polynomial map of the sphere, with `χ = 2` on both sides.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.ramificationDegree_spherePolynomial_sq` and
  `TauCeti.RiemannSurface.FiniteHolomorphicMap.branchValues_spherePolynomial_sq`: `z ↦ z²` has
  `R = 2` and branch values `0` and `∞`.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.eulerChar_compl_spherePolynomial_sq`: the
  punctured formula `0 = 2 · 0` for `z ↦ z²`.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.eulerChar_onePoint_eq_spherePolynomial_sq` and
  `FiniteHolomorphicMap.ramificationDegree_spherePolynomial_sq_eq_of_eulerChar`:
  the branched-cover formula for `z ↦ z²`, and `R = 2` recovered from it.
* `FiniteHolomorphicMap.eulerChar_onePoint_eq_spherePolynomial_four_mul_X_mul_one_sub_X`:
  the same for the Chebyshev map `z ↦ 4z(1 - z)`, punctured at its branch values `1` and `∞`.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.ramificationDegree_spherePolynomial_X`: the identity
  map of the sphere has `R = 0`, also recovered from the branched-cover formula.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §17 (the Riemann–Hurwitz formula).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4 (the Hurwitz formula and its examples).
-/

public noncomputable section

open OnePoint Polynomial Set
open scoped Manifold

namespace TauCeti.RiemannSurface

/-! ### The Riemann sphere punctured at a finite point and `∞` -/

/-- The punctured plane `ℂ \ {0}` embeds in the Riemann sphere by `z ↦ z + c`, with image the
complement of `c` and `∞`. -/
private theorem range_coe_add_compl_zero (c : ℂ) :
    range (fun z : ({0}ᶜ : Set ℂ) ↦ (((z : ℂ) + c : ℂ) : OnePoint ℂ)) =
      ({(c : OnePoint ℂ), ∞}ᶜ : Set (OnePoint ℂ)) := by
  ext x
  induction x using OnePoint.rec with
  | infty => simp
  | coe w =>
    simp only [mem_range, Subtype.exists, mem_compl_iff, mem_singleton_iff, coe_eq_coe,
      mem_insert_iff, coe_ne_infty, or_false]
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hw
      exact ⟨w - c, by simpa [sub_eq_zero] using hw, by simp⟩

/-- **The twice-punctured Riemann sphere has finite CW type.** Deleting `∞` and a finite point `c`
from `OnePoint ℂ` leaves the punctured plane, which is homeomorphic to a circle times an open
half-line. -/
instance finiteCWType_compl_coe_pair_infty (c : ℂ) :
    FiniteCWType ↥({(c : OnePoint ℂ), ∞}ᶜ : Set (OnePoint ℂ)) := by
  have hemb : Topology.IsEmbedding
      (fun z : ({0}ᶜ : Set ℂ) ↦ (((z : ℂ) + c : ℂ) : OnePoint ℂ)) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.comp
      ((Homeomorph.addRight c).isEmbedding.comp Topology.IsEmbedding.subtypeVal)
  have : ContractibleSpace (Ioi (0 : ℝ)) := (convex_Ioi 0).contractibleSpace nonempty_Ioi
  exact ((hemb.toHomeomorph.trans (Homeomorph.setCongr (range_coe_add_compl_zero c))).symm.trans
    (homeomorphUnitSphereProd ℂ)).finiteCWType

/-- **The twice-punctured Riemann sphere has Euler characteristic `0`**: each of the two
punctures lowers the Euler characteristic `2` of the sphere by one. -/
@[simp]
theorem eulerChar_compl_coe_pair_infty (c : ℂ) :
    eulerChar ↥({(c : OnePoint ℂ), ∞}ᶜ : Set (OnePoint ℂ)) = 0 := by
  rw [eulerChar_compl_of_finite (E := ℂ) (toFinite _), eulerChar_onePoint,
    Complex.finrank_real_complex, ncard_pair (coe_ne_infty c)]
  norm_num

/-- The polynomial `X ^ 2` is nonconstant. -/
theorem natDegree_X_sq_pos : 0 < (X ^ 2 : ℂ[X]).natDegree := by
  simp

namespace FiniteHolomorphicMap

variable {p : ℂ[X]}

/-! ### The ramification degree of a polynomial map of the sphere -/

/-- At a finite point `z`, the local multiplicity of a polynomial map of the sphere, minus one, is
the multiplicity of `z` as a critical point of `p`. -/
private theorem localMultiplicity_onePointMap_eval_coe_sub_one (hp : 0 < p.natDegree) (z : ℂ) :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ p.eval z) (z : OnePoint ℂ) - 1 =
      p.derivative.rootMultiplicity z := by
  rw [localMultiplicity_onePointMap_eval_coe hp,
    ← derivative_rootMultiplicity_of_root (by simp), derivative_sub, derivative_C, sub_zero]

/-- **The ramification degree of a polynomial map of the sphere.** The extension of a polynomial
`p` of degree `d ≥ 1` to the Riemann sphere has ramification degree `2d - 2`: it is `d - 1` at `∞`,
and the critical points of `p`, counted with multiplicity, contribute the degree `d - 1` of the
derivative. -/
theorem ramificationDegree_spherePolynomial (hp : 0 < p.natDegree) :
    ramificationDegree (spherePolynomial hp) = 2 * p.natDegree - 2 := by
  classical
  have hd : p.derivative ≠ 0 := derivative_ne_zero.mpr hp.ne'
  let s : Finset (OnePoint ℂ) :=
    insert ∞ (p.derivative.roots.toFinset.map ⟨((↑) : ℂ → OnePoint ℂ), coe_injective⟩)
  have hsupp : Function.support
      (fun x ↦ localMultiplicity (OnePoint.map fun z : ℂ ↦ p.eval z) x - 1) ⊆ s := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact Finset.mem_insert_self _ _
    | coe z =>
      rw [Function.mem_support, localMultiplicity_onePointMap_eval_coe_sub_one hp] at hx
      refine Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ ?_)
      rw [Multiset.mem_toFinset, mem_roots hd]
      by_contra h
      exact hx (rootMultiplicity_eq_zero h)
  rw [ramificationDegree_def, coe_spherePolynomial, finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_insert (by simp), Finset.sum_map, localMultiplicity_onePointMap_eval_infty hp]
  simp only [Function.Embedding.coeFn_mk, localMultiplicity_onePointMap_eval_coe_sub_one hp]
  simp_rw [← count_roots]
  rw [Multiset.toFinset_sum_count_eq, IsAlgClosed.card_roots_eq_natDegree (k := ℂ),
    natDegree_derivative]
  omega

/-- **The branched-cover formula for polynomial maps of the sphere.** Both sides on `OnePoint ℂ`
have Euler characteristic `2`, and a polynomial map of degree `d` has ramification degree
`2d - 2`, so `χ(OnePoint ℂ) = d · χ(OnePoint ℂ) - R`, that is `2 = 2d - (2d - 2)`. -/
theorem eulerChar_onePoint_eq_spherePolynomial (hp : 0 < p.natDegree) :
    eulerChar (OnePoint ℂ) =
      degree (spherePolynomial hp) * eulerChar (OnePoint ℂ) -
        ramificationDegree (spherePolynomial hp) := by
  rw [ramificationDegree_spherePolynomial hp, coe_spherePolynomial, degree_onePointMap_eval hp,
    eulerChar_onePoint, Complex.finrank_real_complex]
  push_cast [show 2 ≤ 2 * p.natDegree by omega]
  ring

/-! ### The squaring map `z ↦ z²` -/

/-- The derivative `2z` of `z²` vanishes only at `0`. -/
private theorem isRoot_derivative_X_sq_iff {z : ℂ} :
    (derivative (X ^ 2 : ℂ[X])).IsRoot z ↔ z = 0 := by
  simp

/-- The squaring map of the sphere has degree `2`. -/
theorem degree_spherePolynomial_sq : degree (spherePolynomial natDegree_X_sq_pos) = 2 := by
  rw [coe_spherePolynomial, degree_onePointMap_eval natDegree_X_sq_pos]
  simp

/-- The squaring map of the sphere is ramified of index `2` at `0`. -/
theorem localMultiplicity_spherePolynomial_sq_zero :
    localMultiplicity (spherePolynomial natDegree_X_sq_pos) ((0 : ℂ) : OnePoint ℂ) = 2 := by
  rw [coe_spherePolynomial, localMultiplicity_onePointMap_eval_coe natDegree_X_sq_pos]
  simpa using rootMultiplicity_X_sub_C_pow (0 : ℂ) 2

/-- The squaring map of the sphere is ramified of index `2` at `∞`. -/
theorem localMultiplicity_spherePolynomial_sq_infty :
    localMultiplicity (spherePolynomial natDegree_X_sq_pos) (∞ : OnePoint ℂ) = 2 := by
  rw [coe_spherePolynomial, localMultiplicity_onePointMap_eval_infty natDegree_X_sq_pos]
  simp

/-- The squaring map of the sphere is unramified away from `0` and `∞`. -/
theorem localMultiplicity_spherePolynomial_sq_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    localMultiplicity (spherePolynomial natDegree_X_sq_pos) (z : OnePoint ℂ) = 1 := by
  rw [coe_spherePolynomial]
  exact localMultiplicity_onePointMap_eval_coe_of_not_isRoot natDegree_X_sq_pos
    (isRoot_derivative_X_sq_iff.not.2 hz)

/-- The squaring map of the sphere has ramification degree `2 · 2 - 2 = 2`, matching its local
multiplicities: index `2` at `0` and at `∞`, and `1` elsewhere. -/
theorem ramificationDegree_spherePolynomial_sq :
    ramificationDegree (spherePolynomial natDegree_X_sq_pos) = 2 := by
  rw [ramificationDegree_spherePolynomial]
  simp

/-- The branch values of the squaring map of the sphere are `0` and `∞`. -/
theorem branchValues_spherePolynomial_sq :
    (spherePolynomial natDegree_X_sq_pos).branchValues = {((0 : ℂ) : OnePoint ℂ), ∞} := by
  have hd : derivative (X ^ 2 : ℂ[X]) ≠ 0 := derivative_ne_zero.mpr natDegree_X_sq_pos.ne'
  have h : (X ^ 2 : ℂ[X]).criticalValues ℂ = {0} := Set.ext fun _ ↦ by
    simp only [mem_criticalValues_self_iff hd, isRoot_derivative_X_sq_iff, exists_eq_left,
      mem_singleton_iff]
    simp [eq_comm]
  rw [branchValues_spherePolynomial (by simp), h, image_singleton, pair_comm]

/-- The preimage of `{0, ∞}` under the squaring map of the sphere is `{0, ∞}`. -/
theorem preimage_spherePolynomial_sq_pair :
    spherePolynomial natDegree_X_sq_pos ⁻¹' {((0 : ℂ) : OnePoint ℂ), ∞} =
      {((0 : ℂ) : OnePoint ℂ), ∞} := by
  ext x
  induction x using OnePoint.rec with
  | infty => simp
  | coe z => simp

/-- **The punctured branched-cover formula for `z ↦ z²`.** Puncturing the target at the branch
values `0` and `∞`, and the source at their preimage, which is again `{0, ∞}`, gives a covering of
degree `2` of the twice-punctured sphere by itself: `χ = 2 · χ`, that is `0 = 2 · 0`. -/
theorem eulerChar_compl_spherePolynomial_sq :
    eulerChar ↥({((0 : ℂ) : OnePoint ℂ), ∞}ᶜ : Set (OnePoint ℂ)) =
      degree (spherePolynomial natDegree_X_sq_pos) *
        eulerChar ↥({((0 : ℂ) : OnePoint ℂ), ∞}ᶜ : Set (OnePoint ℂ)) := by
  have h := (spherePolynomial natDegree_X_sq_pos).eulerChar_compl_preimage
    branchValues_spherePolynomial_sq.subset
  convert h using 3 <;> rw [preimage_spherePolynomial_sq_pair]

/-- **The branched-cover formula for `z ↦ z²`**, obtained from the general formula by puncturing
at the branch values `0` and `∞`: `χ(OnePoint ℂ) = 2 · χ(OnePoint ℂ) - R`. -/
theorem eulerChar_onePoint_eq_spherePolynomial_sq :
    eulerChar (OnePoint ℂ) =
      degree (spherePolynomial natDegree_X_sq_pos) * eulerChar (OnePoint ℂ) -
        ramificationDegree (spherePolynomial natDegree_X_sq_pos) := by
  have := (spherePolynomial natDegree_X_sq_pos).finite_branchValues
  rw [branchValues_spherePolynomial_sq] at this
  exact eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset _ this
    branchValues_spherePolynomial_sq.subset

/-- The branched-cover formula alone recovers `R = 2` for `z ↦ z²`, independently of the local
multiplicity count: `2 = 2 · 2 - R`. -/
theorem ramificationDegree_spherePolynomial_sq_eq_of_eulerChar :
    (ramificationDegree (spherePolynomial natDegree_X_sq_pos) : ℤ) = 2 := by
  have h := eulerChar_onePoint_eq_spherePolynomial_sq
  rw [degree_spherePolynomial_sq, eulerChar_onePoint, Complex.finrank_real_complex] at h
  linear_combination h

/-! ### The Chebyshev map `z ↦ 4z(1 - z)` -/

/-- The Chebyshev map `z ↦ 4z(1 - z)` of the sphere, of degree `2`, has ramification degree `2`,
at `1/2` and at `∞`. -/
theorem ramificationDegree_spherePolynomial_four_mul_X_mul_one_sub_X :
    ramificationDegree (spherePolynomial natDegree_four_mul_X_mul_one_sub_X_pos) = 2 := by
  rw [ramificationDegree_spherePolynomial, natDegree_four_mul_X_mul_one_sub_X]

/-- **The branched-cover formula for `z ↦ 4z(1 - z)`**, obtained from the general formula by
puncturing at the branch values `1` and `∞`: `χ(OnePoint ℂ) = 2 · χ(OnePoint ℂ) - R`. -/
theorem eulerChar_onePoint_eq_spherePolynomial_four_mul_X_mul_one_sub_X :
    eulerChar (OnePoint ℂ) =
      degree (spherePolynomial natDegree_four_mul_X_mul_one_sub_X_pos) * eulerChar (OnePoint ℂ) -
        ramificationDegree (spherePolynomial natDegree_four_mul_X_mul_one_sub_X_pos) :=
  eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset _ (toFinite _)
    branchValues_spherePolynomial_four_mul_X_mul_one_sub_X.subset

/-! ### The identity map -/

/-- The identity map of the sphere, the extension of the polynomial `X`, has degree `1`. -/
theorem degree_spherePolynomial_X : degree (spherePolynomial (p := X) (by simp)) = 1 := by
  rw [coe_spherePolynomial, degree_onePointMap_eval (by simp)]
  simp

/-- The identity map of the sphere is unramified: its ramification degree is `0`. -/
theorem ramificationDegree_spherePolynomial_X :
    ramificationDegree (spherePolynomial (p := X) (by simp)) = 0 := by
  rw [ramificationDegree_spherePolynomial]
  simp

/-- The branched-cover formula alone recovers `R = 0` for the identity map of the sphere,
puncturing at `0` and `∞`, which contain the (empty) set of branch values. -/
theorem ramificationDegree_spherePolynomial_X_eq_of_eulerChar :
    (ramificationDegree (spherePolynomial (p := X) (by simp)) : ℤ) = 0 := by
  have hS : (spherePolynomial (p := X) (by simp)).branchValues ⊆ {((0 : ℂ) : OnePoint ℂ), ∞} := by
    intro y hy
    obtain ⟨x, rfl, hx⟩ := (mem_branchValues_iff _ _).1 hy
    rw [coe_spherePolynomial] at hx
    induction x using OnePoint.rec with
    | infty =>
      rw [localMultiplicity_onePointMap_eval_infty (by simp)] at hx
      simp at hx
    | coe z =>
      rw [one_lt_localMultiplicity_onePointMap_eval_coe_iff (by simp)] at hx
      simp at hx
  have h := eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset _ (toFinite _) hS
  rw [degree_spherePolynomial_X, Nat.cast_one, one_mul] at h
  linear_combination h

/-! ### Checks -/

/-- The sign error `χ(X) = deg f · χ(Y) + R(f)` fails on `z ↦ z²`, where it would read
`2 = 2 · 2 + 2`. -/
example : (2 : ℤ) ≠ 2 * 2 + 2 := by norm_num

/-- A model in which a puncture left the Euler characteristic unchanged would turn the punctured
formula `0 = 2 · 0` for `z ↦ z²` into the false `2 = 2 · 2`. -/
example : (2 : ℤ) ≠ 2 * 2 := by norm_num

end FiniteHolomorphicMap

end TauCeti.RiemannSurface
