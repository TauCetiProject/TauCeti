/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.RingTheory.StableRange
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import TauCeti.RingTheory.Jacobson.Basic

/-!
# Stable range one for semilocal rings

A possibly noncommutative ring `R` is semilocal when its quotient `R ⧸ Ring.jacobson R` by the
Jacobson radical is a semisimple ring; local rings and Artinian rings are semilocal. This file
proves Bass's theorem that every semilocal ring has Bass stable range at most `1`
(`TauCeti.HasStableRangeLE R 1`). Through the stability theorems for `K₁`
(`TauCeti.AlgebraicK1.mk_surjective` and
`TauCeti.AlgebraicK1.quotientFinElementarySubgroupEquiv`), every class of `K₁(R)` of such a ring is
then the class of a `1 × 1` invertible matrix, and `GLₙ(R) ⧸ Eₙ(R) ≃* K₁(R)` for `n ≥ 2`.

## Implementation notes

The proof has three steps.

* **Endomorphisms of a finite-dimensional vector space.** Let `f, g` be endomorphisms of a
  finite-dimensional vector space `V` over a division ring with `range f + range g = V`. Choose a
  complement `C ⊆ range g` of `range f`. It has the dimension of `ker f`, so an isomorphism
  `ker f ≃ C`, lifted through `g` and composed with a projection onto `ker f`, gives `h` with
  `f + g * h` injective, hence a unit. Matrix rings over division rings are opposites of such
  endomorphism rings, and stable range is insensitive to passing to the opposite ring.
* **Semisimple rings.** By the Wedderburn–Artin theorem a semisimple ring is a finite product of
  matrix rings over division rings, and stable range is computed factorwise.
* **Lifting modulo the Jacobson radical.** Stable range does not change modulo a two-sided ideal
  contained in the Jacobson radical: a row that becomes unimodular after reduction is already
  unimodular, because `1 + x` is a unit for every `x` in the radical.

The hypothesis is containment in the Jacobson radical, not Mathlib's `Ideal.IsRadical`: the prime
ideal `5ℤ` is radical in that sense, but `ℤ` does not have stable range one although `ℤ ⧸ 5ℤ` does.

## Main results

* `TauCeti.hasStableRangeLE_one_moduleEnd`: the endomorphism ring of a finite-dimensional vector
  space over a division ring has stable range at most `1`.
* `TauCeti.hasStableRangeLE_one_matrix`: a matrix ring over a division ring has stable range at
  most `1`.
* `IsSemisimpleRing.hasStableRangeLE_one`: a semisimple ring has stable range at most `1`.
* `TauCeti.hasStableRangeLE_iff_of_surjective_of_ker_le_jacobson` and
  `TauCeti.hasStableRangeLE_quotient_iff_of_le_jacobson`: stable range does not change modulo a
  two-sided ideal contained in the Jacobson radical.
* `TauCeti.hasStableRangeLE_one_of_isSemisimpleRing`: a semilocal ring has stable range at most
  `1`.

## References

* H. Bass, *K-theory and stable algebra*, Publ. Math. IHÉS 22 (1964), §6.
* L. N. Vaserstein, *Stable rank of rings and dimensionality of topological spaces*, Functional
  Analysis and Its Applications 5 (1971), 102–110, Lemma 3.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter I, Exercises 1.5(c) and 1.12(v).
-/

public section

open Module

namespace TauCeti

/-! ## Endomorphisms of a finite-dimensional vector space and matrices over a division ring -/

/-- The endomorphism ring of a finite-dimensional vector space `V` over a division ring `K` has
stable range at most `1`: if `range f + range g = V`, then `f + g * h` is invertible for some
endomorphism `h`. -/
theorem hasStableRangeLE_one_moduleEnd (K V : Type*) [DivisionRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] : HasStableRangeLE (Module.End K V) 1 := by
  refine hasStableRangeLE_one_iff.mpr fun f g x y hfg ↦ ?_
  -- The ranges of `g` and `f` together span `V`, since `v = g (y v) + f (x v)`.
  have hcod : Codisjoint (LinearMap.range g) (LinearMap.range f) := by
    refine codisjoint_iff.mpr (eq_top_iff.mpr fun v _ ↦ ?_)
    have hv : g (y v) + f (x v) = v := by
      simpa [add_comm] using LinearMap.congr_fun hfg v
    exact hv ▸ Submodule.add_mem_sup (LinearMap.mem_range_self g _)
      (LinearMap.mem_range_self f _)
  -- A complement `C ⊆ range g` of `range f` has the dimension of `ker f`.
  obtain ⟨C, hCg, hC⟩ := hcod.exists_isCompl
  have hdim : finrank K (LinearMap.ker f) = finrank K C := by
    have h₁ := LinearMap.finrank_range_add_finrank_ker f
    have h₂ := Submodule.finrank_add_eq_of_isCompl hC
    omega
  let e : LinearMap.ker f ≃ₗ[K] C := LinearEquiv.ofFinrankEq _ _ hdim
  -- Lift `e : ker f ≃ C ⊆ range g` through `g`, and project `V` onto `ker f`.
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property g.rangeRestrict
    (Submodule.inclusion hCg ∘ₗ e.toLinearMap) g.surjective_rangeRestrict
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  let π := Submodule.projectionOnto (LinearMap.ker f) W hW
  refine ⟨φ ∘ₗ π, (LinearMap.isUnit_iff_ker_eq_bot _).mpr (LinearMap.ker_eq_bot'.mpr ?_)⟩
  intro v hv
  have hgφ : g (φ (π v)) = (e (π v) : V) := by
    simpa using congrArg (fun F : LinearMap.ker f →ₗ[K] LinearMap.range g ↦ (F (π v) : V)) hφ
  have hsum : f v + (e (π v) : V) = 0 := by
    simpa [mul_apply_eq_comp, hgφ] using hv
  -- `f v ∈ range f` and `e (π v) ∈ C` sum to zero, so both vanish.
  have hfv : f v = 0 := by
    refine Submodule.disjoint_def.mp hC.disjoint (f v) ?_ (LinearMap.mem_range_self f v)
    rw [eq_neg_of_add_eq_zero_left hsum]
    exact neg_mem (e (π v)).property
  have hπv : π v = 0 := by simpa [hfv] using hsum
  have hπ : π v = ⟨v, hfv⟩ := Submodule.projectionOnto_apply_left hW ⟨v, hfv⟩
  simpa using congrArg Subtype.val (hπ.symm.trans hπv)

/-- A matrix ring over a division ring has stable range at most `1`. -/
theorem hasStableRangeLE_one_matrix (D ι : Type*) [DivisionRing D] [Fintype ι] [DecidableEq ι] :
    HasStableRangeLE (Matrix ι ι D) 1 :=
  -- `Matrix ι ι D` is the opposite of the endomorphism ring of the vector space `ι → D`.
  (matrixRingEquivEndVecMulOpposite (A := D) (ι := ι)).hasStableRangeLE_iff.mpr <|
    hasStableRangeLE_mop_iff.mpr <| hasStableRangeLE_one_moduleEnd D (ι → D)

end TauCeti

/-! ## Semisimple rings -/

/-- A semisimple ring has stable range at most `1`. -/
theorem IsSemisimpleRing.hasStableRangeLE_one (R : Type*) [Ring R] [IsSemisimpleRing R] :
    TauCeti.HasStableRangeLE R 1 := by
  -- By the Wedderburn–Artin theorem `R` is a finite product of matrix rings over division rings.
  obtain ⟨n, D, d, _, -, ⟨e⟩⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  exact e.hasStableRangeLE_iff.mpr <| TauCeti.hasStableRangeLE_pi_iff.mpr fun i ↦
    TauCeti.hasStableRangeLE_one_matrix (D i) (Fin (d i))

namespace TauCeti

/-! ## Lifting modulo the Jacobson radical -/

/-- Stable range does not change along a surjective ring homomorphism whose kernel lies in the
Jacobson radical. -/
theorem hasStableRangeLE_iff_of_surjective_of_ker_le_jacobson {R S : Type*} [Ring R] [Ring S]
    {f : R →+* S} (hf : Function.Surjective f) (hker : RingHom.ker f ≤ Ring.jacobson R) {s : ℕ} :
    HasStableRangeLE R s ↔ HasStableRangeLE S s := by
  refine ⟨fun h ↦ h.of_surjective hf, fun h ↦
    hasStableRangeLE_iff_exists_sum_eq_one.mpr fun a b hab ↦ ?_⟩
  obtain ⟨c', d', hcd'⟩ := hasStableRangeLE_iff_exists_sum_eq_one.mp h (f ∘ a) (f ∘ b)
    (by simpa [map_sum] using congrArg f hab)
  choose c hc using fun i ↦ hf (c' i)
  choose d hd using fun i ↦ hf (d' i)
  -- The lifted shortened row pairs with `d` to an element `x` that is `1` modulo the radical, so
  -- `x` is a unit and `d * x⁻¹` witnesses unimodularity.
  set x := ∑ i, (a (Fin.castSucc i) + a (Fin.last s) * c i) * d i with hx
  have hx1 : x - 1 ∈ Ring.jacobson R :=
    hker <| by simpa [RingHom.mem_ker, hx, map_sum, hc, hd, sub_eq_zero] using hcd'
  obtain ⟨u, hu⟩ : IsUnit x := by
    simpa using Ring.mem_jacobson_iff_isUnit_one_add_mul_left.mp hx1 1
  refine ⟨c, fun i ↦ d i * ↑u⁻¹, ?_⟩
  simp_rw [← mul_assoc, ← Finset.sum_mul, ← hx, ← hu, Units.mul_inv]

/-- Stable range does not change modulo a two-sided ideal `I` contained in the Jacobson radical:
`R ⧸ I` has stable range at most `s` exactly when `R` does. -/
theorem hasStableRangeLE_quotient_iff_of_le_jacobson {R : Type*} [Ring R] {I : Ideal R}
    [I.IsTwoSided] (hI : I ≤ Ring.jacobson R) {s : ℕ} :
    HasStableRangeLE (R ⧸ I) s ↔ HasStableRangeLE R s :=
  (hasStableRangeLE_iff_of_surjective_of_ker_le_jacobson Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker])).symm

/-! ## Semilocal rings -/

/-- **Bass.** A semilocal ring, one whose quotient by its Jacobson radical is semisimple, has stable
range at most `1`. -/
theorem hasStableRangeLE_one_of_isSemisimpleRing (R : Type*) [Ring R]
    [IsSemisimpleRing (R ⧸ Ring.jacobson R)] : HasStableRangeLE R 1 :=
  (hasStableRangeLE_quotient_iff_of_le_jacobson le_rfl).mp
    (IsSemisimpleRing.hasStableRangeLE_one _)

end TauCeti
