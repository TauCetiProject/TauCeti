/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic

/-!
# The cup pairing on the middle cohomology of a compact oriented manifold

Let `N` be a compact oriented `n`-manifold with a continuous map `f : N → X`, and let `k + k = n`.
The **cup pairing** `TauCeti.HomologicalOrientation.cupPairing` is the integral bilinear form

`(x, y) ↦ ⟨x ⌣ y, f_*[N]⟩`

on `Hᵏ(X; ℤ)`, built from the integral cup product `TopCat.integralCup` and the evaluation
`TauCeti.HomologicalOrientation.evalFundamentalClass` on the image of the fundamental class. For
`f = id` and `n = 4`, `k = 2` it is the intersection form of the four-manifold `N`. By graded
commutativity it is symmetric when `k` is even (`TauCeti.HomologicalOrientation.isSymm_cupPairing`).

If `a` has odd degree, the cup square `(a ⌣ c) ⌣ (a ⌣ c)` has order at most two
(`TopCat.integralCup_integralCup_add_self_eq_zero_of_odd`), so its pairing with `f_*[N]` is an
integer `y` with `y + y = 0`, and hence vanishes
(`TauCeti.HomologicalOrientation.cupPairing_integralCup_self_eq_zero`). Consequently a
characteristic class `w` of the cup pairing (`LinearMap.BilinForm.IsCharacteristic`, so that
`⟨w ⌣ x, f_*[N]⟩ ≡ ⟨x ⌣ x, f_*[N]⟩` modulo `2` for every `x`) pairs evenly with every such
product: `⟨w ⌣ a ⌣ c, f_*[N]⟩ ∈ 2ℤ`
(`TauCeti.HomologicalOrientation.two_dvd_cupPairing_integralCup`).

On a closed oriented four-manifold, the first Chern class `l = c₁(L)` of the determinant line of a
`Spinᶜ` structure is characteristic for the intersection form. For degree-one classes `a` and `b`
the integer `⟨l ⌣ a ⌣ b, [X]⟩` is therefore even; its half is the integral alternating form
`TauCeti.HomologicalOrientation.halfCupInsertionForm` of
`TauCeti.AlgebraicTopology.Cohomology.InsertionForm`, which enters the Seiberg–Witten
wall-crossing formula for `b₂⁺ = 1`.

## Main definitions

* `TauCeti.HomologicalOrientation.cupPairing`: the bilinear form `(x, y) ↦ ⟨x ⌣ y, f_*[N]⟩` on
  `Hᵏ(X; ℤ)`, `k + k = n`.

## Main results

* `TauCeti.HomologicalOrientation.isSymm_cupPairing`: the cup pairing is symmetric in even degree.
* `TauCeti.HomologicalOrientation.cupPairing_integralCup_self_eq_zero`:
  `⟨(a ⌣ c) ⌣ (a ⌣ c), f_*[N]⟩ = 0` for `a` of odd degree.
* `TauCeti.HomologicalOrientation.two_dvd_cupPairing_integralCup`: a characteristic class `w`
  has `⟨w ⌣ (a ⌣ c), f_*[N]⟩` even for `a` of odd degree.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 3.2 and 3.3.
* C. Okonek and A. Teleman, *Seiberg–Witten invariants for manifolds with `b₊ = 1`, and the
  universal wall crossing formula*, Internat. J. Math. 7 (1996), 811–832.
-/

public section

noncomputable section

namespace TauCeti

namespace HomologicalOrientation

variable {N E : Type} [TopologicalSpace N] [T2Space N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E N]
  [CompactSpace N] {n : ℕ} (o : HomologicalOrientation N E n) (hn : Module.finrank ℝ E = n)
  {X : Type} [TopologicalSpace X]

/-- **The cup pairing** of a compact oriented `n`-manifold `f : N → X` on `Hᵏ(X; ℤ)`, `k + k = n`:
the integral bilinear form `(x, y) ↦ ⟨x ⌣ y, f_*[N]⟩`. For `f = id` and `k = 2`, `n = 4` it is the
intersection form of a four-manifold. -/
def cupPairing (f : C(N, X)) (k : ℕ) (h : k + k = n) :
    LinearMap.BilinForm ℤ ((TopCat.of X).integralCohomology k) :=
  LinearMap.mk₂ ℤ
    (fun x y ↦ o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) f
      ((TopCat.of X).integralCup k k n h x y))
    (fun x x' y ↦ by simp) (fun c x y ↦ by simp) (fun x y y' ↦ by simp) (fun c x y ↦ by simp)

/-- The value of the cup pairing, `⟨x ⌣ y, f_*[N]⟩`. -/
theorem cupPairing_apply (f : C(N, X)) (k : ℕ) (h : k + k = n)
    (x y : (TopCat.of X).integralCohomology k) :
    o.cupPairing hn f k h x y =
      o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) f ((TopCat.of X).integralCup k k n h x y) :=
  (rfl)

/-- The cup pairing is symmetric in even degree, since `y ⌣ x = (-1)^(k k) x ⌣ y`. -/
theorem isSymm_cupPairing (f : C(N, X)) {k : ℕ} (hk : Even k) (h : k + k = n) :
    (o.cupPairing hn f k h).IsSymm := by
  refine ⟨fun x y ↦ ?_⟩
  rw [cupPairing_apply, cupPairing_apply, (TopCat.of X).integralCup_gradedComm h h x y,
    (hk.mul_right k).neg_one_pow, one_zsmul]

/-- **The cup square of a product with an odd factor pairs to zero**: if `a` has odd degree, then
`⟨(a ⌣ c) ⌣ (a ⌣ c), f_*[N]⟩ = 0`. -/
theorem cupPairing_integralCup_self_eq_zero (f : C(N, X)) {p q k : ℕ} (hp : Odd p)
    (hk : p + q = k) (h : k + k = n) (a : (TopCat.of X).integralCohomology p)
    (c : (TopCat.of X).integralCohomology q) :
    o.cupPairing hn f k h ((TopCat.of X).integralCup p q k hk a c)
      ((TopCat.of X).integralCup p q k hk a c) = 0 := by
  have h2 := congrArg (o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) f)
    ((TopCat.of X).integralCup_integralCup_add_self_eq_zero_of_odd hp hk h a c)
  rw [map_add, map_zero] at h2
  -- `ℤ` is torsion free, so an integer `y` with `y + y = 0` vanishes.
  have hy (y : ℤ) (hy : y + y = 0) : y = 0 := by omega
  exact hy _ h2

/-- **Characteristic classes pair evenly with products having an odd factor**: if `w` is
characteristic for the cup pairing and `a` has odd degree, then `⟨w ⌣ (a ⌣ c), f_*[N]⟩` is even.
For the first Chern class `l` of a `Spinᶜ` structure on a closed oriented four-manifold and
degree-one classes `a`, `c`, this is the evenness of `⟨l ⌣ a ⌣ c, [X]⟩`. -/
theorem two_dvd_cupPairing_integralCup (f : C(N, X)) {p q k : ℕ} (hp : Odd p)
    (hk : p + q = k) (h : k + k = n) {w : (TopCat.of X).integralCohomology k}
    (hw : (o.cupPairing hn f k h).IsCharacteristic w) (a : (TopCat.of X).integralCohomology p)
    (c : (TopCat.of X).integralCohomology q) :
    2 ∣ o.cupPairing hn f k h w ((TopCat.of X).integralCup p q k hk a c) := by
  simpa [o.cupPairing_integralCup_self_eq_zero hn f hp hk h a c] using
    LinearMap.BilinForm.isCharacteristic_iff.1 hw ((TopCat.of X).integralCup p q k hk a c)

end HomologicalOrientation

end TauCeti
