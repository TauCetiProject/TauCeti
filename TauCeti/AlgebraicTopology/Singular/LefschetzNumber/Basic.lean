/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Zeta
public import TauCeti.Topology.Homotopy.Contractible

/-!
# The Lefschetz number and the Lefschetz zeta function of a continuous map

Let `k` be a field and `f : X → X` a continuous self-map of a topological space. The map `f` acts
on the singular homology `Hₙ(X; k)` by the linear map `f_*` (`ContinuousMap.singularHomologyMap`),
and its **Lefschetz number** is the alternating sum of the traces

`L(f) = ∑ₙ (-1) ^ n tr (f_* : Hₙ(X; k) → Hₙ(X; k))`

(`ContinuousMap.lefschetzNumber`). The sum is a `finsum`: it is the honest alternating sum as soon
as the homology vanishes in all but finitely many degrees
(`ContinuousMap.lefschetzNumber_eq_sum`), for instance for a space of finite CW type, such as a
compact smooth manifold. The trace of an endomorphism of an infinite-dimensional space is `0` by
convention (`LinearMap.trace`), so the Lefschetz number is meaningful when each `Hₙ(X; k)` is
finite-dimensional.

The Lefschetz number depends only on the action of `f` on homology, so it is a homotopy invariant
(`ContinuousMap.lefschetzNumber_eq_of_homotopic`). The trace identity `tr (g f) = tr (f g)` gives
`L(g ∘ f) = L(f ∘ g)` for maps `f : X → Y` and `g : Y → X` between spaces whose homology is
finite-dimensional in every degree, such as spaces of finite CW type
(`ContinuousMap.lefschetzNumber_comp_comm`). The identity map has Lefschetz number the
Euler characteristic (`ContinuousMap.lefschetzNumber_id`), and every self-map of a contractible
space has Lefschetz number one (`ContinuousMap.lefschetzNumber_of_contractibleSpace`), so its
Lefschetz zeta function below is `(1 - t)⁻¹`.

The iterates of `f` act on homology by the powers of `f_*`
(`ContinuousMap.singularHomologyMap_iterate`), so their Lefschetz numbers are the alternating sums
of the traces of these powers. Over a field of characteristic zero the **Lefschetz zeta function**

`ζ_f = exp (∑ₙ L(fⁿ) tⁿ / n)`

(`ContinuousMap.lefschetzZeta`) is a formal power series defined for every continuous map, whether
or not its fixed points are isolated. For a space of finite CW type it is the alternating product
of the reversed characteristic polynomials `det (1 - t f_*)` of the actions of `f` on homology:

`ζ_f = ∏ₙ det (1 - t f_* | Hₙ(X; k)) ^ (-1) ^ (n + 1)`

(`ContinuousMap.lefschetzZeta_eq_prod_odd_mul_inv`, and without inverses
`ContinuousMap.lefschetzZeta_mul_prod_even_eq_prod_odd`). The finite set of degrees in this product
is any set outside which the homology vanishes. This is the trace–determinant formula
`LinearMap.subst_exp_eq_prod_odd_mul_inv`, applied to the graded action of `f` on homology. When
every iterate of `f` has only nondegenerate fixed points, the Lefschetz fixed point theorem
identifies `L(fⁿ)` with the signed count of the fixed points of `fⁿ`, and `ζ_f` becomes the
dynamical zeta function of `f`; that theorem is not proved here.

## Main definitions

* `ContinuousMap.lefschetzNumber k f`: the Lefschetz number of `f` over the field `k`.
* `ContinuousMap.lefschetzZeta k f`: the Lefschetz zeta function `exp (∑ₙ L(fⁿ) tⁿ / n)`.

## Main results

* `ContinuousMap.lefschetzNumber_eq_sum`: the Lefschetz number as a finite alternating sum.
* `ContinuousMap.lefschetzNumber_eq_of_homotopic`: homotopy invariance.
* `ContinuousMap.lefschetzNumber_comp_comm`: `L(g ∘ f) = L(f ∘ g)`.
* `ContinuousMap.lefschetzNumber_id`: the Lefschetz number of the identity is the Euler
  characteristic.
* `ContinuousMap.lefschetzNumber_of_contractibleSpace`: a self-map of a contractible space has
  Lefschetz number one.
* `ContinuousMap.lefschetzZeta_eq_prod_odd_mul_inv`: the Lefschetz zeta function is the
  alternating product of the polynomials `det (1 - t f_* | Hₙ(X; k))`.
* `ContinuousMap.lefschetzZeta_of_contractibleSpace`: on a contractible space it is `(1 - t)⁻¹`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.C (the Lefschetz number).
* S. Smale, *Differentiable dynamical systems*, Bull. Amer. Math. Soc. 73 (1967), 747–817 (the
  Lefschetz zeta function and its determinant formula).
-/

public section

noncomputable section

open CategoryTheory Module TauCeti
open scoped PowerSeries

universe u

namespace ContinuousMap

variable (k : Type u) [Field k] {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The **Lefschetz number** of a continuous self-map `f` over a field `k`: the alternating sum
`∑ₙ (-1) ^ n tr (f_* : Hₙ(X; k) → Hₙ(X; k))` of the traces of its actions on singular homology.
It is a `finsum`, the honest alternating sum when the homology vanishes in all but finitely many
degrees (`ContinuousMap.lefschetzNumber_eq_sum`). -/
def lefschetzNumber (f : C(X, X)) : k :=
  ∑ᶠ n : ℕ, (-1) ^ n * LinearMap.trace k _ (singularHomologyMap k n f)

variable {k}

/-- The Lefschetz number is the alternating sum of the traces of the actions on homology. -/
theorem lefschetzNumber_def (f : C(X, X)) :
    f.lefschetzNumber k = ∑ᶠ n : ℕ, (-1) ^ n * LinearMap.trace k _ (singularHomologyMap k n f) :=
  (rfl)

/-- If the singular homology of `X` vanishes outside a finite set `s` of degrees, the Lefschetz
number of a self-map `f` is the finite alternating sum of the traces of its actions on homology in
the degrees of `s`. -/
theorem lefschetzNumber_eq_sum {s : Finset ℕ}
    (hs : ∀ n ∉ s, Subsingleton (((singularChains k).obj (TopCat.of X)).homology n))
    (f : C(X, X)) :
    f.lefschetzNumber k =
      ∑ n ∈ s, (-1) ^ n * LinearMap.trace k _ (singularHomologyMap k n f) := by
  refine finsum_eq_sum_of_support_subset _ fun n hn ↦ ?_
  by_contra h
  have := hs n h
  refine hn ?_
  dsimp only
  rw [Subsingleton.elim (singularHomologyMap k n f) 0, map_zero, mul_zero]

/-- **Homotopy invariance.** Homotopic self-maps have the same Lefschetz number. -/
theorem lefschetzNumber_eq_of_homotopic {f g : C(X, X)} (H : f.Homotopic g) :
    f.lefschetzNumber k = g.lefschetzNumber k := by
  simp_rw [lefschetzNumber_def, singularHomologyMap_eq_of_homotopic k _ H]

/-- **Commutativity.** For maps `f : X → Y` and `g : Y → X` between spaces whose singular homology
is finite-dimensional in every degree, such as spaces of finite CW type, the composites `g ∘ f` and
`f ∘ g` have the same Lefschetz number, since `tr (g_* f_*) = tr (f_* g_*)` in every degree. -/
theorem lefschetzNumber_comp_comm
    [∀ n, FiniteDimensional k (((singularChains k).obj (TopCat.of X)).homology n)]
    [∀ n, FiniteDimensional k (((singularChains k).obj (TopCat.of Y)).homology n)]
    (f : C(X, Y)) (g : C(Y, X)) :
    (g.comp f).lefschetzNumber k = (f.comp g).lefschetzNumber k := by
  simp_rw [lefschetzNumber_def, singularHomologyMap_comp']
  exact finsum_congr fun n ↦ by rw [LinearMap.trace_comp_comm']

/-- The Lefschetz number of the identity map of a space of finite CW type is its Euler
characteristic. -/
@[simp]
theorem lefschetzNumber_id [FiniteCWType X] :
    (ContinuousMap.id X).lefschetzNumber k = eulerChar X := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (eventually_isZero_singularHomology_of_finiteCWType X (ModuleCat.of k k))
  rw [eulerChar_eq_finsum_finrank_singularHomology X k,
    ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range hN]
  simp_rw [singularHomologyFunctor_obj_obj] at hN
  rw [lefschetzNumber_eq_sum (s := Finset.range N)
      (fun n hn ↦ ModuleCat.isZero_iff_subsingleton.1 (hN n (by simpa using hn)))]
  push_cast
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [singularHomologyMap_id', LinearMap.trace_id, singularHomologyFunctor_obj_obj]

/-- Every self-map of a contractible space has Lefschetz number one: it is homotopic to the
identity, whose Lefschetz number is the Euler characteristic `1`. -/
theorem lefschetzNumber_of_contractibleSpace [ContractibleSpace X] (f : C(X, X)) :
    f.lefschetzNumber k = 1 := by
  rw [lefschetzNumber_eq_of_homotopic (homotopic_of_contractibleSpace f (ContinuousMap.id X)),
    lefschetzNumber_id, eulerChar_of_contractibleSpace, Int.cast_one]

/-! ### Iterates and the Lefschetz zeta function -/

variable (k) in
/-- The **Lefschetz zeta function** of a continuous self-map `f` over a field `k` of characteristic
zero: the formal power series `exp (∑ₙ L(fⁿ) tⁿ / n)` built from the Lefschetz numbers of the
iterates of `f`. -/
def lefschetzZeta [Algebra ℚ k] (f : C(X, X)) : k⟦X⟧ :=
  (PowerSeries.exp k).subst (PowerSeries.mk fun n ↦
    (n : ℚ)⁻¹ • (⟨f^[n], f.continuous.iterate n⟩ : C(X, X)).lefschetzNumber k)

/-- The Lefschetz zeta function is the exponential of the series `∑ₙ L(fⁿ) tⁿ / n`. -/
theorem lefschetzZeta_def [Algebra ℚ k] (f : C(X, X)) :
    f.lefschetzZeta k = (PowerSeries.exp k).subst (PowerSeries.mk fun n ↦
      (n : ℚ)⁻¹ • (⟨f^[n], f.continuous.iterate n⟩ : C(X, X)).lefschetzNumber k) :=
  (rfl)

/-- If the homology of `X` vanishes outside a finite set `s` of degrees, the Lefschetz zeta
function of `f` is the exponential of `∑ₙ (∑_{i ∈ s} (-1) ^ i tr (f_* ^ n | Hᵢ(X; k))) tⁿ / n`. -/
private theorem lefschetzZeta_eq_subst [Algebra ℚ k] {s : Finset ℕ}
    (hs : ∀ n ∉ s, Subsingleton (((singularChains k).obj (TopCat.of X)).homology n))
    (f : C(X, X)) :
    f.lefschetzZeta k = (PowerSeries.exp k).subst (PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ •
      ∑ i ∈ s, (-1) ^ i * LinearMap.trace k _ (singularHomologyMap k i f ^ n)) := by
  simp_rw [lefschetzZeta_def, lefschetzNumber_eq_sum hs, singularHomologyMap_iterate]

/-- **The Lefschetz zeta function as a product**, stated without inverses. Let `X` have
finite-dimensional singular homology over a field `k` of characteristic zero, vanishing outside a
finite set `s` of degrees, as for a space of finite CW type. Multiplied by the reversed
characteristic polynomials `det (1 - t f_* | Hᵢ(X; k))` of the actions of `f` in the even degrees
of `s`, the Lefschetz zeta function of `f` is the product of those in the odd degrees. -/
theorem lefschetzZeta_mul_prod_even_eq_prod_odd [Algebra ℚ k]
    [∀ n, FiniteDimensional k (((singularChains k).obj (TopCat.of X)).homology n)]
    {s : Finset ℕ}
    (hs : ∀ n ∉ s, Subsingleton (((singularChains k).obj (TopCat.of X)).homology n))
    (f : C(X, X)) :
    f.lefschetzZeta k * ∏ i ∈ s with Even i, ((singularHomologyMap k i f).charpoly.reverse : k⟦X⟧) =
      ∏ i ∈ s with Odd i, ((singularHomologyMap k i f).charpoly.reverse : k⟦X⟧) := by
  rw [lefschetzZeta_eq_subst hs]
  exact LinearMap.subst_exp_mul_prod_even_eq_prod_odd s fun i ↦ singularHomologyMap k i f

/-- **The determinant formula for the Lefschetz zeta function.** Let `X` have finite-dimensional
singular homology over a field `k` of characteristic zero, vanishing outside a finite set `s` of
degrees, as for a space of finite CW type. The Lefschetz zeta function of a self-map `f` is the
alternating product

`ζ_f = ∏_{i ∈ s} det (1 - t f_* | Hᵢ(X; k)) ^ (-1) ^ (i + 1)`

of the reversed characteristic polynomials of the actions of `f` on homology. -/
theorem lefschetzZeta_eq_prod_odd_mul_inv [Algebra ℚ k]
    [∀ n, FiniteDimensional k (((singularChains k).obj (TopCat.of X)).homology n)]
    {s : Finset ℕ}
    (hs : ∀ n ∉ s, Subsingleton (((singularChains k).obj (TopCat.of X)).homology n))
    (f : C(X, X)) :
    f.lefschetzZeta k =
      (∏ i ∈ s with Odd i, ((singularHomologyMap k i f).charpoly.reverse : k⟦X⟧)) *
        (∏ i ∈ s with Even i, ((singularHomologyMap k i f).charpoly.reverse : k⟦X⟧))⁻¹ := by
  rw [lefschetzZeta_eq_subst hs]
  exact LinearMap.subst_exp_eq_prod_odd_mul_inv s fun i ↦ singularHomologyMap k i f

/-- The Lefschetz zeta function of a self-map of a contractible space is `(1 - t)⁻¹`: every iterate
has Lefschetz number one, so `ζ_f = exp (∑ₙ tⁿ / n)`. -/
theorem lefschetzZeta_of_contractibleSpace [Algebra ℚ k] [ContractibleSpace X] (f : C(X, X)) :
    f.lefschetzZeta k = (1 - PowerSeries.X)⁻¹ := by
  -- `exp (∑ₙ tⁿ / n)` is the zeta function of the identity of a line, the `1 × 1` matrix `1`.
  have hrev : ((1 : Matrix (Fin 1) (Fin 1) k).charpolyRev : k⟦X⟧) = 1 - PowerSeries.X := by
    simp [Matrix.charpolyRev, Matrix.det_unique]
  rw [lefschetzZeta_def, ← hrev, ← Matrix.subst_exp_eq_inv_charpolyRev]
  simp [lefschetzNumber_of_contractibleSpace]

end ContinuousMap
