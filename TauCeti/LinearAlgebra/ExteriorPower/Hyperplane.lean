/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Set.PowersetCard
public import TauCeti.InformationTheory.Coding.EuclideanDual
public import TauCeti.LinearAlgebra.ExteriorPower.LinearForms

import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.Matrix.Dual

/-!
# Normal vectors and Plücker coordinates of hyperplanes

Let `K` be a field and `ι` a finite linearly ordered type. A hyperplane `U` in `ι → K` — a
subspace with `finrank K U + 1 = Fintype.card ι` — has one-dimensional Euclidean dual
`U.euclideanDual`, so it is cut out by a single nonzero normal vector `a : ι → K` via
`x ∈ U ↔ x ⬝ᵥ a = 0`, unique up to nonzero scalar multiplication.

For any linearly independent family `x : Fin p → ι → K` in `U` with `p + 1 = Fintype.card ι`,
complementary minors (`TauCeti.exists_plucker_eq_mul_plucker_compl_or_eq_neg`) identify the
coordinates `a i` of any normal vector, up to a common nonzero scalar and signs, with the Plücker
coordinates `plucker x (omitOne hm i)` at the `(Fintype.card ι - 1)`-element subsets omitting `i`.
In particular, `plucker x (omitOne hm i) = 0 ↔ a i = 0` (`Submodule.exists_normal`).

When `l : ι → Dual K (ι → K)` is a linearly independent family of linear forms on `ι → K`,
applying this coordinate characterization after the change of coordinates `LinearMap.pi l` and its
dot-product contragredient expresses `a` as a linear combination of the coefficient vectors of
those forms `l i` for which the `(Fintype.card ι - 1)`-wedge form
`wedgeForms l p (omitOne hm i)` does not vanish on `plucker x`
(`TauCeti.mem_span_of_forall_dotProduct_eq_zero`). At least one such wedge form is nonzero
whenever `plucker x ≠ 0` (`TauCeti.exists_wedgeForms_omitOne_ne_zero`). In Diophantine
approximation this locates the normal vector of a hyperplane spanned by an approximation domain
inside a subspace determined solely by the nonvanishing pattern of the wedge forms.

## Main results

* `TauCeti.exists_eq_mul_plucker_omitOne_or_eq_neg` and `TauCeti.plucker_omitOne_eq_zero_iff`:
  a nonzero vector orthogonal to `p` linearly independent vectors in `K^ι` (`p + 1 = #ι`) has
  `i`-th coordinate proportional up to sign to `plucker x (omitOne hm i)`, hence vanishing
  simultaneously with it.
* `Submodule.exists_normal`: every hyperplane `U` in `K^ι` admits a nonzero normal vector `a`
  cutting out `U` by `x ⬝ᵥ a = 0` whose vanishing coordinates match the vanishing `omitOne`
  Plücker coordinates of any basis of `U`.
* `TauCeti.exists_wedgeForms_omitOne_ne_zero`: for linearly independent forms `l`, every nonzero
  vector in `powersetCard ι p → K` (`p + 1 = #ι`) has a nonvanishing `omitOne` wedge form.
* `TauCeti.mem_span_of_forall_dotProduct_eq_zero`: any normal vector to the hyperplane spanned by
  `x` lies in the span of the coefficient vectors of the forms `l i` whose `omitOne hm i` wedge
  form does not vanish at `plucker x`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §2.8 and Lemma 7.5.21.
* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the absolute Subspace Theorem*,
  J. Reine Angew. Math. **548** (2002), Lemmas 12.3–12.4.
-/

public section

open Matrix Module Set Set.powersetCard

namespace TauCeti

variable {K ι : Type*} [Field K] [LinearOrder ι] [Fintype ι] {p : ℕ}

/-- Let `x` be `p` linearly independent vectors in `ι → K`, where `p + 1 = Fintype.card ι`, and
let `a` be a nonzero vector orthogonal to every `x r`. Up to a common nonzero scalar `c` and
signs, each coordinate `a i` equals the Plücker coordinate `plucker x (omitOne hm i)`. -/
theorem exists_eq_mul_plucker_omitOne_or_eq_neg (hm : p + 1 = Fintype.card ι)
    {x : Fin p → ι → K} (hx : LinearIndependent K x) {a : ι → K} (ha : a ≠ 0)
    (hxa : ∀ r, x r ⬝ᵥ a = 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ i : ι,
      a i = c * plucker x (omitOne hm i) ∨ a i = -(c * plucker x (omitOne hm i)) := by
  have ha_li : LinearIndependent K ![a] := linearIndependent_unique_iff.2 ha
  obtain ⟨c, hc, h⟩ := exists_plucker_eq_mul_plucker_compl_or_eq_neg hm hx ha_li fun r j ↦ by
    fin_cases j
    exact hxa r
  refine ⟨c, hc, fun i ↦ ?_⟩
  simpa only [plucker_ofSingleton, Matrix.cons_val_zero, ← omitOne_apply] using h (ofSingleton i)

/-- For `p` linearly independent vectors `x` in `ι → K` with `p + 1 = Fintype.card ι` and any
nonzero vector `a` orthogonal to every `x r`, the Plücker coordinate `plucker x (omitOne hm i)`
vanishes if and only if `a i = 0`. -/
theorem plucker_omitOne_eq_zero_iff (hm : p + 1 = Fintype.card ι)
    {x : Fin p → ι → K} (hx : LinearIndependent K x) {a : ι → K} (ha : a ≠ 0)
    (hxa : ∀ r, x r ⬝ᵥ a = 0) (i : ι) :
    plucker x (omitOne hm i) = 0 ↔ a i = 0 := by
  obtain ⟨c, hc, h⟩ := exists_eq_mul_plucker_omitOne_or_eq_neg hm hx ha hxa
  rcases h i with hi | hi <;> simp [hi, hc]

/-- For linearly independent forms `l : ι → Dual K (ι → K)` and `p + 1 = Fintype.card ι`, every
nonzero vector `w : powersetCard ι p → K` has at least one index `i` at which
`wedgeForms l p (omitOne hm i) w ≠ 0`. -/
theorem exists_wedgeForms_omitOne_ne_zero (hm : p + 1 = Fintype.card ι)
    {l : ι → Dual K (ι → K)} (hl : LinearIndependent K l) {w : powersetCard ι p → K}
    (hw : w ≠ 0) :
    ∃ i : ι, wedgeForms l p (omitOne hm i) w ≠ 0 := by
  by_contra! h
  refine hw ((linearIndependent_wedgeForms hl p).eq_zero_of_forall_apply_eq_zero
    (Module.finrank_fintype_fun_eq_card K).symm fun T ↦ ?_)
  simpa using h ((omitOne hm).symm T)

/-- If `x` is a linearly independent family of `p` vectors in `ι → K` with
`p + 1 = Fintype.card ι`, `a` is a nonzero vector orthogonal to every `x r`, and `l` is a linearly
independent family of linear forms on `ι → K`, then `a` lies in the span of the coefficient
vectors `j ↦ l i (Pi.single j 1)` of those forms `l i` whose `omitOne hm i` wedge form does not
vanish at `plucker x`. -/
theorem mem_span_of_forall_dotProduct_eq_zero (hm : p + 1 = Fintype.card ι)
    {l : ι → Dual K (ι → K)} (hl : LinearIndependent K l)
    {x : Fin p → ι → K} (hx : LinearIndependent K x) {a : ι → K} (ha : a ≠ 0)
    (hxa : ∀ r, x r ⬝ᵥ a = 0) :
    a ∈ Submodule.span K ((fun i j ↦ l i (Pi.single j 1)) ''
      {i | wedgeForms l p (omitOne hm i) (plucker x) ≠ 0}) := by
  let Φ : (ι → K) ≃ₗ[K] (ι → K) := LinearEquiv.ofBijective (LinearMap.pi l) hl.pi_bijective
  let a' : ι → K := Φ.dotProductContragredient a
  have ha' : a' ≠ 0 := by simpa [a'] using ha
  let y : Fin p → ι → K := fun r ↦ Φ (x r)
  have hy : LinearIndependent K y := hx.map' Φ.toLinearMap Φ.ker
  have hya' (r : Fin p) : y r ⬝ᵥ a' = 0 := by
    rw [dotProduct_comm, Φ.dotProductContragredient_apply_dotProduct_apply, dotProduct_comm]
    exact hxa r
  -- In the coordinates defined by `l`, the `i`-th coordinate of `a'` vanishes with the `i`-th
  -- omitting-one wedge form.
  have hzero (i : ι) : a' i = 0 ↔ wedgeForms l p (omitOne hm i) (plucker x) = 0 := by
    rw [← plucker_omitOne_eq_zero_iff hm hy ha' hya' i]
    have hpi : plucker y (omitOne hm i) = wedgeForms l p (omitOne hm i) (plucker x) :=
      plucker_pi_apply l x (omitOne hm i)
    rw [hpi]
  -- Expand `a` coordinatewise against the coefficient vectors of `l`.
  have ha_eq : a = ∑ i, a' i • fun j ↦ l i (Pi.single j 1) := by
    ext j
    calc
      a j = a ⬝ᵥ Pi.single j 1 := by simp
      _ = a' ⬝ᵥ Φ (Pi.single j 1) :=
        (Φ.dotProductContragredient_apply_dotProduct_apply a (Pi.single j 1)).symm
      _ = (∑ i, a' i • fun k ↦ l i (Pi.single k 1)) j := by simp [Φ, dotProduct]
  rw [ha_eq]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  by_cases hi : wedgeForms l p (omitOne hm i) (plucker x) = 0
  · simp [(hzero i).mpr hi]
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

end TauCeti

namespace Submodule

open TauCeti

/-- Every hyperplane `U` in `ι → K` is cut out by a nonzero normal vector `a : ι → K` via
`x ∈ U ↔ x ⬝ᵥ a = 0`, and for any linearly independent family `x : Fin p → ι → K` in `U` with
`p + 1 = Fintype.card ι`, the Plücker coordinate `plucker x (omitOne hm i)` vanishes if and only if
`a i = 0`. -/
theorem exists_normal {K ι : Type*} [Field K] [LinearOrder ι] [Fintype ι]
    {U : Submodule K (ι → K)} (hU : finrank K U + 1 = Fintype.card ι) :
    ∃ a : ι → K, a ≠ 0 ∧ (∀ x, x ∈ U ↔ x ⬝ᵥ a = 0) ∧
      ∀ {p : ℕ} (hm : p + 1 = Fintype.card ι) {x : Fin p → ι → K},
        LinearIndependent K x → (∀ r, x r ∈ U) →
        ∀ i : ι, (plucker x (omitOne hm i) = 0 ↔ a i = 0) := by
  have hdim : finrank K U.euclideanDual = 1 := by
    have := finrank_add_finrank_euclideanDual U
    omega
  obtain ⟨⟨a, ha_mem⟩, ha₀, -⟩ := finrank_eq_one_iff'.mp hdim
  have ha : a ≠ 0 := by simpa using ha₀
  have hUa : ∀ x ∈ U, x ⬝ᵥ a = 0 := mem_euclideanDual.mp ha_mem
  refine ⟨a, ha, fun x ↦ mem_iff_dotProduct_eq_zero_of_finrank_add_one hU ha hUa,
    fun {p} hm {x} hx hxr i ↦ plucker_omitOne_eq_zero_iff hm hx ha (fun r ↦ hUa _ (hxr r)) i⟩

end Submodule
