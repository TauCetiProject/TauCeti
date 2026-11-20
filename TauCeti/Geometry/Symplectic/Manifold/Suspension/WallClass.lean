/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.AlgebraicTopology.Cohomology.InsertionForm
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Chamber

/-!
# The Seiberg–Witten wall class of a symplectic suspension with `b₁ = 1`

On a closed oriented four-manifold `X`, the wall-crossing formula of Seiberg–Witten theory with
`b₁(X) > 0` involves the class

`u = ½ Σ_(i<j) ⟨l ⌣ αᵢ ⌣ αⱼ, [X]⟩ νᵢ νⱼ`

on the Picard torus, where `l` is the first Chern class of the determinant line of the `Spinᶜ`
structure, `α₁, …, α_b` is a basis of `H¹(X; ℤ)` and `ν₁, …, ν_b` the dual coordinates. Its
coefficients are the values of the integral alternating form
`TauCeti.HomologicalOrientation.halfCupInsertionForm`, `(a, b) ↦ ⟨l ⌣ a ⌣ b, [X]⟩ / 2`, which is
defined when `l` is characteristic for the cup pairing.

This file computes `u` for the labels of a symplectic suspension, in the notation of
`TauCeti.Geometry.Symplectic.Manifold.Suspension.Chamber`. Let `φ` be an area-preserving
diffeomorphism of a closed connected oriented surface of genus `g` whose mapping torus `Y_φ` has
`b₁(Y_φ) = 1`, and let `X = (ℝ / ℤ)_s × Y_φ`. Then `H¹(X; ℤ)` has the basis `aₛ = [ds]`,
`aₜ = [dt]`, and the class `t = [ds ∧ dt]` is the cup product `aₛ ⌣ aₜ`. With a lift `v` of the
fibre class, `v · t = 1`, `t · t = 0`, the canonical class `κ = (2g - 2) v` and a label
`e = a v + c t`, both modulo torsion, the determinant class `l = 2e - κ` gives

`⟨l ⌣ aₛ ⌣ aₜ, [X]⟩ = l · t = 2q`,  `q = a + 1 - g`

(`TauCeti.SmoothMappingTorus.halfCupInsertionForm_two_smul_sub_apply_eq`). Since an alternating
form on a free module of rank two is determined by its value on a basis, the wall class is

`u = q νₛ νₜ`

(`TauCeti.SmoothMappingTorus.halfCupInsertionForm_two_smul_sub_eq_smul_det`): the half insertion
form is `q` times the determinant form of the basis `(aₛ, aₜ)`. Explicitly
`(x, y) ↦ q (νₛ(x) νₜ(y) - νₜ(x) νₛ(y))`
(`TauCeti.SmoothMappingTorus.halfCupInsertionForm_two_smul_sub_apply`), and `u` vanishes exactly
when `q = 0` (`TauCeti.SmoothMappingTorus.halfCupInsertionForm_two_smul_sub_eq_zero_iff`).

The order `(aₛ, aₜ)` is the order of the product homology orientation `e₀ ∧ i[ds] ∧ i[dt] ∧ e₊`.
The half insertion form needs `l = 2e - κ` to be characteristic for the cup pairing, which holds
because the canonical class is. That, the cup pairing values, the cup product `aₛ ⌣ aₜ = t`, the
basis of `H¹(X; ℤ)` and the coordinates of `e` and `κ` are hypotheses: they are the topology of
the product, which is separate from this computation. Torsion is retained, since
`e` and `κ` are only assumed to agree with their coordinate expressions up to elements of finite
order.

## References

* C. Okonek and A. Teleman, *Seiberg–Witten invariants for manifolds with `b₊ = 1`, and the
  universal wall crossing formula*, Internat. J. Math. 7 (1996), 811–832.
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127–158.
-/

public section

namespace TauCeti

namespace SmoothMappingTorus

open HomologicalOrientation

variable {N E : Type} [TopologicalSpace N] [T2Space N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E N]
  [CompactSpace N] {n : ℕ} (o : HomologicalOrientation N E n) (hn : Module.finrank ℝ E = n)
  {X : Type} [TopologicalSpace X] (f : C(N, X)) (h : 2 + 2 = n)
  {v t e κ : (TopCat.of X).integralCohomology 2} {a c g : ℤ}
  (hl : (o.cupPairing hn f 2 h).IsCharacteristic ((2 : ℤ) • e - κ))
  (ht : o.cupPairing hn f 2 h t t = 0) (hvt : o.cupPairing hn f 2 h v t = 1)
  (he : IsOfFinAddOrder (e - (a • v + c • t))) (hκ : IsOfFinAddOrder (κ - (2 * g - 2) • v))
include ht hvt he hκ

/-- **The wall class on the product pair.** Let `l = 2e - κ` with `e = a v + c t` and
`κ = (2g - 2) v` modulo torsion, `l` characteristic for the cup pairing, `v · t = 1` and
`t · t = 0`. If `t = aₛ ⌣ aₜ`, the half insertion form of `l` takes the value `q = a + 1 - g` on
`(aₛ, aₜ)`: `⟨l ⌣ aₛ ⌣ aₜ, f_*[N]⟩ / 2 = q`. -/
theorem halfCupInsertionForm_two_smul_sub_apply_eq
    {aₛ aₜ : (TopCat.of X).integralCohomology 1}
    (hst : (TopCat.of X).integralCup 1 1 2 rfl aₛ aₜ = t) :
    o.halfCupInsertionForm hn f h ((2 : ℤ) • e - κ) hl ![aₛ, aₜ] =
      a + 1 - g := by
  have h2 := o.two_mul_halfCupInsertionForm_apply hn f h hl ![aₛ, aₜ]
  rw [cupInsertionForm_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero,
    hst, apply_two_smul_sub_right_eq ht hvt he hκ] at h2
  linarith

/-- **The wall class is `q νₛ νₜ`.** Under the hypotheses of
`TauCeti.SmoothMappingTorus.halfCupInsertionForm_two_smul_sub_apply_eq`, for a basis `b` of
`H¹(X; ℤ)` with `b 0 ⌣ b 1 = t`, the half insertion form of `l = 2e - κ` is `q = a + 1 - g` times
the determinant form of `b`. -/
theorem halfCupInsertionForm_two_smul_sub_eq_smul_det
    (b : Module.Basis (Fin 2) ℤ ((TopCat.of X).integralCohomology 1))
    (hst : (TopCat.of X).integralCup 1 1 2 rfl (b 0) (b 1) = t) :
    o.halfCupInsertionForm hn f h ((2 : ℤ) • e - κ) hl =
      (a + 1 - g) • b.det := by
  rw [AlternatingMap.eq_smul_basis_det b (o.halfCupInsertionForm hn f h _ _)]
  congr 1
  have hb : (⇑b : Fin 2 → _) = ![b 0, b 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hb]
  exact halfCupInsertionForm_two_smul_sub_apply_eq o hn f h hl ht hvt he hκ hst

/-- **Coordinates of the wall class.** Under the hypotheses of
`TauCeti.SmoothMappingTorus.halfCupInsertionForm_two_smul_sub_eq_smul_det`, with `νₛ` and `νₜ`
the coordinates of the basis `b`, the half insertion form of `l = 2e - κ` is
`(x, y) ↦ q (νₛ(x) νₜ(y) - νₜ(x) νₛ(y))`, `q = a + 1 - g`. -/
theorem halfCupInsertionForm_two_smul_sub_apply
    (b : Module.Basis (Fin 2) ℤ ((TopCat.of X).integralCohomology 1))
    (hst : (TopCat.of X).integralCup 1 1 2 rfl (b 0) (b 1) = t)
    (x y : (TopCat.of X).integralCohomology 1) :
    o.halfCupInsertionForm hn f h ((2 : ℤ) • e - κ) hl ![x, y] =
      (a + 1 - g) * (b.coord 0 x * b.coord 1 y - b.coord 1 x * b.coord 0 y) := by
  rw [halfCupInsertionForm_two_smul_sub_eq_smul_det o hn f h hl ht hvt he hκ b hst,
    smul_apply, smul_eq_mul, Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, Module.Basis.coord_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- **Vanishing of the wall class.** Under the hypotheses of
`TauCeti.SmoothMappingTorus.halfCupInsertionForm_two_smul_sub_eq_smul_det`, the half insertion
form of `l = 2e - κ` vanishes exactly when `q = a + 1 - g` does. -/
theorem halfCupInsertionForm_two_smul_sub_eq_zero_iff
    (b : Module.Basis (Fin 2) ℤ ((TopCat.of X).integralCohomology 1))
    (hst : (TopCat.of X).integralCup 1 1 2 rfl (b 0) (b 1) = t) :
    o.halfCupInsertionForm hn f h ((2 : ℤ) • e - κ) hl = 0 ↔ a + 1 - g = 0 := by
  rw [halfCupInsertionForm_two_smul_sub_eq_smul_det o hn f h hl ht hvt he hκ b hst]
  refine ⟨fun h0 ↦ ?_, fun hq ↦ by rw [hq, zero_smul]⟩
  simpa [Module.Basis.det_self] using congrArg (fun F ↦ F b) h0

end SmoothMappingTorus

end TauCeti
