/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pairing
public import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Insertion forms of degree-one classes

Let `X` be a space and `Hⁿ(X; ℤ)` its integral singular cohomology, with the integral cup product
`TopCat.integralCup`. For degree-one classes `a₁, …, a_r ∈ H¹(X; ℤ)` let
`a₁ ⌣ ⋯ ⌣ a_r ∈ Hʳ(X; ℤ)` be their iterated cup product `TopCat.integralCupProd`, a multilinear
map. An iterated product with a repeated factor has order at most two
(`TopCat.integralCupProd_add_self_eq_zero`). This weaker statement than vanishing suffices for the
integer pairing below, and no division by two is made in cohomology.

Now let `N` be a compact oriented `n`-manifold with a continuous map `f : N → X`, let `β` be a
class of degree `q`, and let `r + q = n`. The **insertion form**
`TauCeti.HomologicalOrientation.cupInsertionForm` is

`(a₁, …, a_r) ↦ ⟨a₁ ⌣ ⋯ ⌣ a_r ⌣ β, f_*[N]⟩ ∈ ℤ`.

It is an alternating `ℤ`-multilinear form on `H¹(X; ℤ)`: a repeated argument gives a value `y`
with `y + y = 0`, and `ℤ` is torsion free. For `r = 0` it is the evaluation `⟨β, f_*[N]⟩`
(`TauCeti.HomologicalOrientation.cupInsertionForm_zero`). Composing with a linear map
`ν : G → H¹(X; ℤ)` (`AlternatingMap.compLinearMap`) gives alternating forms on any abelian group
`G`.

For `r = 2` and a class `l` of degree two on a four-manifold, `n = 4`, the insertion form is
`(a, b) ↦ ⟨l ⌣ (a ⌣ b), f_*[N]⟩`, the cup pairing `TauCeti.HomologicalOrientation.cupPairing` of
`l` with `a ⌣ b`. When `l` is characteristic for the cup pairing, all its values are even
(`TauCeti.HomologicalOrientation.two_dvd_cupInsertionForm_two`), and halving them gives the
integral alternating form `TauCeti.HomologicalOrientation.halfCupInsertionForm`,
`(a, b) ↦ ⟨l ⌣ a ⌣ b, f_*[N]⟩ / 2`. For the first Chern class `l` of a `Spinᶜ` structure on a
closed oriented four-manifold `X`, its values on a basis `α₁, …, α_b` of `H¹(X; ℤ)` are the integer
coefficients of the class `u = ½ Σ_(i<j) ⟨l ⌣ αᵢ ⌣ αⱼ, [X]⟩ νᵢ νⱼ` on the Picard torus in the
Seiberg–Witten wall-crossing formula.

These are the integral Seiberg–Witten invariants with insertions of loops, once the moduli space is
available: for a compact oriented moduli space `M` of dimension `d = r + 2m`, the class `β = μᵐ`
of a power of the point class, and the map `ν : H₁(X; ℤ) → H¹(M; ℤ)` given by slant product with
the first Chern class of the universal line, the invariant is the alternating form
`(γ₁, …, γ_r) ↦ ⟨ν(γ₁) ⌣ ⋯ ⌣ ν(γ_r) ⌣ μᵐ, [M]⟩`.

## Main definitions

* `TauCeti.HomologicalOrientation.cupInsertionForm`: the alternating form
  `(a₁, …, a_r) ↦ ⟨a₁ ⌣ ⋯ ⌣ a_r ⌣ β, f_*[N]⟩`.
* `TauCeti.HomologicalOrientation.halfCupInsertionForm`: for `l` characteristic, the integral
  alternating form `(a, b) ↦ ⟨l ⌣ a ⌣ b, f_*[N]⟩ / 2`.

## Main results

* `TauCeti.HomologicalOrientation.cupInsertionForm_apply`: the value of the insertion form, and
  `TauCeti.HomologicalOrientation.cupInsertionForm_zero`: for `r = 0` it is `⟨β, f_*[N]⟩`.
* `TauCeti.HomologicalOrientation.cupInsertionForm_two_apply`: for `r = 2` and `l` of degree two
  it is `(a, b) ↦ ⟨l ⌣ (a ⌣ b), f_*[N]⟩`.
* `TauCeti.HomologicalOrientation.two_dvd_cupInsertionForm_two`: for `l` characteristic its values
  are even, and `TauCeti.HomologicalOrientation.two_mul_halfCupInsertionForm_apply`: twice the
  half form is the insertion form.

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

/-- **The insertion form** of a class `β` of degree `q` along a compact oriented `n`-manifold
`f : N → X`, for `q + r = n`: the alternating `ℤ`-multilinear form
`(a₁, …, a_r) ↦ ⟨a₁ ⌣ ⋯ ⌣ a_r ⌣ β, f_*[N]⟩` on `H¹(X; ℤ)`. -/
def cupInsertionForm (f : C(N, X)) {q : ℕ} (β : (TopCat.of X).integralCohomology q) (r : ℕ)
    (h : r + q = n) :
    (TopCat.of X).integralCohomology 1 [⋀^Fin r]→ₗ[ℤ] ℤ where
  toMultilinearMap := MultilinearMap.mk'
    (fun v ↦ o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) f
      ((TopCat.of X).integralCup r q n h ((TopCat.of X).integralCupProd r v) β))
    (fun v i a b ↦ by simp)
    (fun v i c a ↦ by simp)
  map_eq_zero_of_eq' v i j hv hij := by
    have h2 := congrArg (fun x ↦ o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) f
      ((TopCat.of X).integralCup r q n h x β))
      ((TopCat.of X).integralCupProd_add_self_eq_zero r v hv hij)
    simp only [map_add, LinearMap.add_apply, map_zero, LinearMap.zero_apply] at h2
    -- `ℤ` is torsion free, so an integer `y` with `y + y = 0` vanishes.
    have hy (y : ℤ) (hy : y + y = 0) : y = 0 := by omega
    exact hy _ h2

/-- The value of the insertion form, `⟨a₁ ⌣ ⋯ ⌣ a_r ⌣ β, f_*[N]⟩`. -/
theorem cupInsertionForm_apply (f : C(N, X)) {q : ℕ} (β : (TopCat.of X).integralCohomology q)
    (r : ℕ) (h : r + q = n) (v : Fin r → (TopCat.of X).integralCohomology 1) :
    o.cupInsertionForm hn f β r h v =
      o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) f
        ((TopCat.of X).integralCup r q n h ((TopCat.of X).integralCupProd r v) β) :=
  (rfl)

/-- For `r = 0` the insertion form is the evaluation `⟨β, f_*[N]⟩`. -/
@[simp]
theorem cupInsertionForm_zero (f : C(N, X)) (β : (TopCat.of X).integralCohomology n)
    (v : Fin 0 → (TopCat.of X).integralCohomology 1) :
    o.cupInsertionForm hn f β 0 (zero_add n) v =
      o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) f β := by
  rw [cupInsertionForm_apply, TopCat.integralCupProd_zero,
    TopCat.integralCup_integralCohomologyOne]

/-- For `r = 2` and a class `l` of degree two on a four-manifold, the insertion form is the cup
pairing `(a, b) ↦ ⟨l ⌣ (a ⌣ b), f_*[N]⟩`. -/
theorem cupInsertionForm_two_apply (f : C(N, X)) (h : 2 + 2 = n)
    (l : (TopCat.of X).integralCohomology 2) (v : Fin 2 → (TopCat.of X).integralCohomology 1) :
    o.cupInsertionForm hn f l 2 h v =
      o.cupPairing hn f 2 h l ((TopCat.of X).integralCup 1 1 2 rfl (v 0) (v 1)) := by
  rw [cupInsertionForm_apply, cupPairing_apply, (TopCat.of X).integralCup_gradedComm h h,
    TopCat.integralCupProd_succ, TopCat.integralCupProd_succ, TopCat.integralCupProd_zero,
    TopCat.integralCup_integralCohomologyOne_right]
  norm_num [Fin.tail]

/-- **Half-integrality**: for a class `l` of degree two that is characteristic for the cup pairing,
every value `⟨l ⌣ (a ⌣ b), f_*[N]⟩` of the insertion form is even. -/
theorem two_dvd_cupInsertionForm_two (f : C(N, X)) (h : 2 + 2 = n)
    {l : (TopCat.of X).integralCohomology 2} (hl : (o.cupPairing hn f 2 h).IsCharacteristic l)
    (v : Fin 2 → (TopCat.of X).integralCohomology 1) : 2 ∣ o.cupInsertionForm hn f l 2 h v := by
  rw [cupInsertionForm_two_apply]
  exact o.two_dvd_cupPairing_integralCup hn f (p := 1) (q := 1) odd_one rfl h hl (v 0) (v 1)

/-- **The half insertion form** of a class `l` of degree two that is characteristic for the cup
pairing of a four-manifold: the integral alternating form `(a, b) ↦ ⟨l ⌣ a ⌣ b, f_*[N]⟩ / 2` on
`H¹(X; ℤ)`, whose values are integers by `two_dvd_cupInsertionForm_two`. -/
def halfCupInsertionForm (f : C(N, X)) (h : 2 + 2 = n) (l : (TopCat.of X).integralCohomology 2)
    (hl : (o.cupPairing hn f 2 h).IsCharacteristic l) :
    (TopCat.of X).integralCohomology 1 [⋀^Fin 2]→ₗ[ℤ] ℤ where
  toMultilinearMap := MultilinearMap.mk' (fun v ↦ o.cupInsertionForm hn f l 2 h v / 2)
    (fun v i x y ↦ by
      rw [AlternatingMap.map_update_add, Int.add_ediv_of_dvd_left
        (o.two_dvd_cupInsertionForm_two hn f h hl _)])
    (fun v i c x ↦ by
      rw [AlternatingMap.map_update_smul, smul_eq_mul, smul_eq_mul,
        Int.mul_ediv_assoc c (o.two_dvd_cupInsertionForm_two hn f h hl _), RingHom.id_apply])
  map_eq_zero_of_eq' v i j hv hij := by
    simp [(o.cupInsertionForm hn f l 2 h).map_eq_zero_of_eq v hv hij]

/-- The value of the half insertion form, half of the insertion form. -/
theorem halfCupInsertionForm_apply (f : C(N, X)) (h : 2 + 2 = n)
    {l : (TopCat.of X).integralCohomology 2} (hl : (o.cupPairing hn f 2 h).IsCharacteristic l)
    (v : Fin 2 → (TopCat.of X).integralCohomology 1) :
    o.halfCupInsertionForm hn f h l hl v = o.cupInsertionForm hn f l 2 h v / 2 :=
  (rfl)

/-- Twice the half insertion form is the insertion form `(a, b) ↦ ⟨l ⌣ (a ⌣ b), f_*[N]⟩`. -/
@[simp]
theorem two_mul_halfCupInsertionForm_apply (f : C(N, X)) (h : 2 + 2 = n)
    {l : (TopCat.of X).integralCohomology 2} (hl : (o.cupPairing hn f 2 h).IsCharacteristic l)
    (v : Fin 2 → (TopCat.of X).integralCohomology 1) :
    2 * o.halfCupInsertionForm hn f h l hl v = o.cupInsertionForm hn f l 2 h v :=
  Int.mul_ediv_cancel' (o.two_dvd_cupInsertionForm_two hn f h hl v)

end HomologicalOrientation

end TauCeti
