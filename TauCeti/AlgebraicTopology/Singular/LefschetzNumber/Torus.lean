/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LefschetzNumber.Basic
public import TauCeti.AlgebraicTopology.Singular.Torus.Exterior
public import TauCeti.Topology.Algebra.Module.Matrix
public import TauCeti.Topology.Category.TopCat.MonObj
import TauCeti.AlgebraicTopology.Singular.Coefficients.BaseChange
import TauCeti.AlgebraicTopology.Singular.Torus.FirstHomology
import TauCeti.LinearAlgebra.ExteriorPower.Trace
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.LinearAlgebra.Matrix.Charpoly.Zeta
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Lefschetz number of a linear endomorphism of a torus

Let `k` be a field. For a commutative topological monoid `G` the Pontryagin product of classes of
degree one induces linear maps `⋀ⁿ H₁(G; k) → Hₙ(G; k)` (`TopCat.pontryaginExteriorPower`),
natural in continuous homomorphisms. When they are bijective, as for a torus, a continuous
homomorphism `f : G → G` acts on `Hₙ(G; k)` as `⋀ⁿ P` for its action `P = f_*` on `H₁(G; k)`
(`TopCat.trace_singularHomologyFunctor_map_eq_trace_exteriorPower_map`).
If moreover `H₁(G; k)` is finite-dimensional, the Lefschetz number of `f` is therefore the
alternating sum of the traces of the exterior powers of `P`, which is

`L(f) = ∑ₙ (-1) ^ n tr (⋀ⁿ P) = det (1 - P)`

(`ContinuousMap.lefschetzNumber_eq_det_id_sub_of_bijective`, through
`LinearMap.sum_neg_one_pow_mul_trace_exteriorPower_map`).

For `p ≠ 0` the Pontryagin maps of the torus `Tⁿ = ι → AddCircle p` are bijective over every
commutative ring (`AddCircle.bijective_pontryaginExteriorPower_pi`, in
`TauCeti.AlgebraicTopology.Singular.Torus.Exterior`). An integer matrix
`A : Matrix ι ι ℤ` acts on `Tⁿ` by the continuous homomorphism `x ↦ A • x` (`Matrix.smulVecHom`),
and on `H₁(Tⁿ; ℤ) = ℤⁿ` by `A`
(`TauCeti.torusFirstHomologyEquiv_homologyMap_smulVecHom`). Over a field `k` of characteristic
zero, flat base change carries this to `H₁(Tⁿ; k)`, so the Lefschetz number of `x ↦ A • x` is

`L(x ↦ A • x) = det (1 - A)`

(`Matrix.lefschetzNumber_smulVecHom`). The iterates of `x ↦ A • x` are the maps of the powers of
`A` (`Matrix.lefschetzNumber_iterate_smulVecHom`), so its Lefschetz zeta function is
`exp (∑ₙ det (1 - Aⁿ) tⁿ / n)` (`Matrix.lefschetzZeta_smulVecHom`). On the two-torus this is
`det (1 - t A) / ((1 - t) (1 - det A t))` (`Matrix.lefschetzZeta_smulVecHom_mul_fin_two`), and for
`det A = 1` it is `det (1 - t A) / (1 - t) ^ 2`
(`Matrix.lefschetzZeta_smulVecHom_fin_two_of_det_eq_one`). For Arnold's cat map
`A = !![2, 1; 1, 1]` this is `(1 - 3 t + t ^ 2) / (1 - t) ^ 2`, and for the identity of the
two-torus it is `(1 - t) ^ 2 / (1 - t) ^ 2 = 1`.

For `A` invertible, every fixed point of `x ↦ A • x` has the Lefschetz sign `sgn det (1 - A)`, and
there are `|det (1 - A)|` of them when `det (1 - A) ≠ 0`, so the Lefschetz number computed here is
the signed count of the fixed points: the Lefschetz fixed-point formula holds for every iterate
(`AddCircle.`
`finsum_sign_det_id_sub_fixedPointDerivative_iterate_generalLinearGroup_smul_eq_lefschetzNumber`,
in `TauCeti.Dynamics.TorusAutomorphism`).

## Main results

* `ContinuousMap.lefschetzNumber_eq_det_id_sub_of_bijective`: when the Pontryagin maps are
  bijective, `L(f) = det (1 - f_*)`, the determinant on `H₁(G; k)`.
* `Matrix.lefschetzNumber_smulVecHom`: the Lefschetz number of `x ↦ A • x` on `ι → AddCircle p`
  is `det (1 - A)`.
* `Matrix.lefschetzNumber_iterate_smulVecHom`: the Lefschetz number of its `n`-th iterate is
  `det (1 - Aⁿ)`.
* `Matrix.lefschetzZeta_smulVecHom`: its Lefschetz zeta function is
  `exp (∑ₙ det (1 - Aⁿ) tⁿ / n)`.
* `Matrix.lefschetzZeta_smulVecHom_mul_fin_two`,
  `Matrix.lefschetzZeta_smulVecHom_fin_two_of_det_eq_one`: the closed forms on the two-torus.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.C (the Lefschetz number) and Section 3.C (the Pontryagin ring of a torus).
* E.-N. Ionel and T. H. Parker, *The Gromov invariants of Ruan–Tian and Taubes*, Math. Res. Lett.
  4 (1997), 521–532, Lemma 3.1 (the homological zeta function of a map of a surface).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory TauCeti

universe u

namespace ContinuousMap

section Exterior

variable {k : Type u} [Field k] {G : Type u} [CommMonoid G] [TopologicalSpace G] [ContinuousMul G]

/-- **The Lefschetz number of a homomorphism of a space whose homology is an exterior algebra.**
Let `G` be a commutative topological monoid whose Pontryagin maps `⋀ⁿ H₁(G; k) → Hₙ(G; k)` are
bijective in every degree, with `H₁(G; k)` finite-dimensional, as for a torus. Then the Lefschetz
number of a continuous homomorphism `f : G → G` is `det (1 - f_*)`, the determinant on
`H₁(G; k)`. -/
theorem lefschetzNumber_eq_det_id_sub_of_bijective
    (hG : ∀ n, Function.Bijective (TopCat.pontryaginExteriorPower k (TopCat.of G) n))
    [FiniteDimensional k (((singularChains k).obj (TopCat.of G)).homology 1)] (f : G →ₜ* G) :
    (f : C(G, G)).lefschetzNumber k =
      (LinearMap.id - singularHomologyMap k 1 (f : C(G, G))).det := by
  set d := Module.finrank k (((singularChains k).obj (TopCat.of G)).homology 1)
  -- the homology vanishes above degree `d`, where the exterior powers of `H₁(G; k)` vanish
  have hs : ∀ n ∉ Finset.range (d + 1),
      Subsingleton (((singularChains k).obj (TopCat.of G)).homology n) := fun n hn ↦ by
    have : Module.finrank k (⋀[k]^n (((singularChains k).obj (TopCat.of G)).homology 1)) = 0 := by
      rw [exteriorPower.finrank_eq, Nat.choose_eq_zero_of_lt (by simpa using hn)]
    have hsub : Subsingleton (⋀[k]^n (((singularChains k).obj (TopCat.of G)).homology 1)) :=
      Module.finrank_zero_iff.1 this
    -- `singularChains k` computes the singular homology functor with coefficients `k = 𝟙_`
    exact @Equiv.subsingleton _ _ (LinearEquiv.ofBijective _ (hG n)).symm.toEquiv hsub
  rw [lefschetzNumber_eq_sum hs, ← LinearMap.sum_neg_one_pow_mul_trace_exteriorPower_map]
  simp_rw [singularHomologyMap_eq_singularHomologyFunctor_map]
  exact Finset.sum_congr rfl fun n _ ↦ congrArg _
    (TopCat.trace_singularHomologyFunctor_map_eq_trace_exteriorPower_map
      (TopCat.ofHom (f : C(G, G))) (hG n))

end Exterior

end ContinuousMap

namespace Matrix

open ContinuousMap

variable {ι : Type} [Fintype ι] [DecidableEq ι] {p : ℝ}

/-- The map `x ↦ A • x` of the torus `ι → AddCircle p`, as a continuous homomorphism of its
multiplicative form. -/
private def smulVecHomMul (A : Matrix ι ι ℤ) :
    Multiplicative (ι → AddCircle p) →ₜ* Multiplicative (ι → AddCircle p) where
  toMonoidHom :=
    (A.smulVecHom (AddCircle p) : (ι → AddCircle p) →+ (ι → AddCircle p)).toMultiplicative
  continuous_toFun := continuous_ofAdd.comp ((A.smulVecHom (AddCircle p)).continuous.comp
    continuous_toAdd)

/-- The map `x ↦ A • x` acts on `H₁(Tⁿ; ℤ) = ℤⁿ` by `A`, so `det (1 - f_*) = det (1 - A)` there. -/
private theorem det_id_sub_singularHomologyMap_smulVecHom_int (A : Matrix ι ι ℤ) (hp : p ≠ 0) :
    (LinearMap.id - singularHomologyMap ℤ 1
        (A.smulVecHom (AddCircle p) : C(ι → AddCircle p, ι → AddCircle p))).det = (1 - A).det := by
  let e := torusFirstHomologyEquiv (fun _ : ι ↦ p) fun _ ↦ hp
  have h : (e : _ →ₗ[ℤ] ι → ℤ) ∘ₗ (LinearMap.id - singularHomologyMap ℤ 1
      (A.smulVecHom (AddCircle p) : C(ι → AddCircle p, ι → AddCircle p))) ∘ₗ
      (e.symm : (ι → ℤ) →ₗ[ℤ] _) = toLin' (1 - A) := by
    refine LinearMap.ext fun v ↦ ?_
    have hv := torusFirstHomologyEquiv_homologyMap_smulVecHom A hp (e.symm v)
    rw [LinearEquiv.apply_symm_apply] at hv
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, map_sub, LinearEquiv.apply_symm_apply, toLin'_apply,
      one_mulVec]
    exact congrArg (v - ·) hv
  rw [← LinearMap.det_conj _ e, h, LinearMap.det_toLin']

/-- **The Lefschetz number of a linear endomorphism of a torus.** For `p ≠ 0`, an integer matrix
`A` and a field `k` of characteristic zero, the map `x ↦ A • x` of the torus `ι → AddCircle p` has
Lefschetz number `det (1 - A)`: it acts on `H_r(Tⁿ; k) = ⋀ʳ kⁿ` by `⋀ʳ A`, and
`∑ᵣ (-1) ^ r tr (⋀ʳ A) = det (1 - A)`. -/
theorem lefschetzNumber_smulVecHom (A : Matrix ι ι ℤ) (k : Type) [Field k] [CharZero k]
    (hp : p ≠ 0) :
    (A.smulVecHom (AddCircle p) : C(ι → AddCircle p, ι → AddCircle p)).lefschetzNumber k =
      ((1 - A).det : k) := by
  have : Module.Free ℤ (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (ι → AddCircle p))) :=
    .of_equiv (torusFirstHomologyEquiv (fun _ : ι ↦ p) fun _ ↦ hp).symm
  have : Module.Finite ℤ (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (ι → AddCircle p))) :=
    .equiv (torusFirstHomologyEquiv (fun _ : ι ↦ p) fun _ ↦ hp).symm
  -- `Multiplicative (ι → AddCircle p)` is a type synonym carrying the topology of the torus, and
  -- `smulVecHomMul A` is `x ↦ A • x` read on it
  have : FiniteDimensional k
      (((singularChains k).obj (TopCat.of (Multiplicative (ι → AddCircle p)))).homology 1) :=
    .equiv (TopCat.singularHomologyBaseChangeEquiv ℤ k (TopCat.of (ι → AddCircle p)) 1)
  have h : (A.smulVecHom (AddCircle p) : C(ι → AddCircle p, ι → AddCircle p)).lefschetzNumber k =
      (LinearMap.id - singularHomologyMap k 1
        (A.smulVecHom (AddCircle p) : C(ι → AddCircle p, ι → AddCircle p))).det :=
    lefschetzNumber_eq_det_id_sub_of_bijective
      (AddCircle.bijective_pontryaginExteriorPower_pi ι hp) (smulVecHomMul A)
  -- flat base change from `ℤ` to `k`
  rw [h, ← det_id_sub_singularHomologyMap_smulVecHom_int A hp, ← eq_intCast (algebraMap ℤ k),
    singularHomologyMap_eq_singularHomologyFunctor_map,
    singularHomologyMap_eq_singularHomologyFunctor_map]
  exact TopCat.det_id_sub_singularHomologyMap_eq_algebraMap _ 1

/-- **The Lefschetz numbers of the iterates of a linear endomorphism of a torus.** For `p ≠ 0`, an
integer matrix `A` and a field `k` of characteristic zero, the `n`-th iterate of the map `x ↦ A • x`
of the torus `ι → AddCircle p` has Lefschetz number `det (1 - Aⁿ)`: it is the map of `Aⁿ`. -/
theorem lefschetzNumber_iterate_smulVecHom (A : Matrix ι ι ℤ) (k : Type) [Field k] [CharZero k]
    (hp : p ≠ 0) (n : ℕ) :
    (⟨(⇑(A.smulVecHom (AddCircle p)))^[n], (A.smulVecHom (AddCircle p)).continuous.iterate n⟩ :
        C(ι → AddCircle p, ι → AddCircle p)).lefschetzNumber k = ((1 - A ^ n).det : k) := by
  have h : (⟨(⇑(A.smulVecHom (AddCircle p)))^[n],
      (A.smulVecHom (AddCircle p)).continuous.iterate n⟩ : C(ι → AddCircle p, ι → AddCircle p)) =
      ((A ^ n).smulVecHom (AddCircle p) : C(ι → AddCircle p, ι → AddCircle p)) :=
    ContinuousMap.ext fun x ↦ congrFun (iterate_smulVecHom (AddCircle p) A n) x
  rw [h, lefschetzNumber_smulVecHom _ k hp]

/-- **The Lefschetz zeta function of a linear endomorphism of a torus.** For `p ≠ 0`, an integer
matrix `A` and a field `k` of characteristic zero, the map `x ↦ A • x` of the torus
`ι → AddCircle p` has Lefschetz zeta function `exp (∑ₙ det (1 - Aⁿ) tⁿ / n)`: its `n`-th iterate is
the map of `Aⁿ`. -/
theorem lefschetzZeta_smulVecHom (A : Matrix ι ι ℤ) (k : Type) [Field k] [Algebra ℚ k]
    (hp : p ≠ 0) :
    (A.smulVecHom (AddCircle p) : C(ι → AddCircle p, ι → AddCircle p)).lefschetzZeta k =
      (PowerSeries.exp k).subst (PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ • ((1 - A ^ n).det : k)) := by
  have := algebraRat.charZero k
  simp_rw [lefschetzZeta_def, ContinuousMap.coe_ofClass, lefschetzNumber_iterate_smulVecHom _ k hp]

/-- **The Lefschetz zeta function of a linear endomorphism of the two-torus.** For `p ≠ 0`, a
`2 × 2` integer matrix `A` and a field `k` of characteristic zero, the map `x ↦ A • x` of the torus
`Fin 2 → AddCircle p` has Lefschetz zeta function `det (1 - t A) / ((1 - t) (1 - det A t))`, stated
without inverses. -/
theorem lefschetzZeta_smulVecHom_mul_fin_two (A : Matrix (Fin 2) (Fin 2) ℤ) (k : Type) [Field k]
    [Algebra ℚ k] (hp : p ≠ 0) :
    (A.smulVecHom (AddCircle p) : C(Fin 2 → AddCircle p, Fin 2 → AddCircle p)).lefschetzZeta k *
        ((1 - PowerSeries.X) * (1 - PowerSeries.C (A.det : k) * PowerSeries.X)) =
      ((A.map (Int.castRingHom k)).charpolyRev : PowerSeries k) := by
  simp_rw [lefschetzZeta_smulVecHom A k hp, intCast_det_one_sub, Matrix.map_pow]
  rw [Int.cast_det]
  exact subst_exp_det_one_sub_pow_mul_fin_two _

/-- **The Lefschetz zeta function of an area-preserving linear map of the two-torus.** For
`p ≠ 0`, a `2 × 2` integer matrix `A` of determinant one and a field `k` of characteristic zero, the
map `x ↦ A • x` of the torus `Fin 2 → AddCircle p` has Lefschetz zeta function
`det (1 - t A) / (1 - t) ^ 2`. For the identity of the torus it is `1`. -/
theorem lefschetzZeta_smulVecHom_fin_two_of_det_eq_one {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : A.det = 1) (k : Type) [Field k] [Algebra ℚ k] (hp : p ≠ 0) :
    (A.smulVecHom (AddCircle p) : C(Fin 2 → AddCircle p, Fin 2 → AddCircle p)).lefschetzZeta k =
      ((A.map (Int.castRingHom k)).charpolyRev : PowerSeries k) * PowerSeries.mk 1 ^ 2 := by
  simp_rw [lefschetzZeta_smulVecHom A k hp, intCast_det_one_sub, Matrix.map_pow]
  exact subst_exp_det_one_sub_pow_fin_two_of_det_eq_one ((Int.castRingHom k).det_map_eq_one hA)

end Matrix
