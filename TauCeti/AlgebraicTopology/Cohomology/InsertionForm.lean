/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Insertion forms of degree-one classes

Let `X` be a space and `Hⁿ(X; ℤ)` its integral singular cohomology, with the integral cup product
`TopCat.integralCup`. For degree-one classes `a₁, …, a_r ∈ H¹(X; ℤ)` let
`a₁ ⌣ ⋯ ⌣ a_r ∈ Hʳ(X; ℤ)` be their iterated cup product (`TopCat.integralCupProd`, nested to the
right, and the unit class for `r = 0`); it is multilinear in the `aᵢ`. Since degree-one classes
anticommute, an iterated product with a repeated factor has order at most two
(`TopCat.integralCupProd_add_self_eq_zero`). The product itself need not vanish, since `Hʳ(X; ℤ)`
can have `2`-torsion, and no division by two is made in cohomology.

Now let `N` be a compact oriented `n`-manifold with a continuous map `f : N → X`, let `β` be a
class of degree `q`, and let `r + q = n`. The **insertion form**
`TauCeti.HomologicalOrientation.cupInsertionForm` is

`(a₁, …, a_r) ↦ ⟨a₁ ⌣ ⋯ ⌣ a_r ⌣ β, f_*[N]⟩ ∈ ℤ`.

It is an alternating `ℤ`-multilinear form on `H¹(X; ℤ)`: a repeated argument gives a value `y`
with `y + y = 0`, and `ℤ` is torsion free. For `r = 0` it is the evaluation `⟨β, f_*[N]⟩`
(`TauCeti.HomologicalOrientation.cupInsertionForm_zero`). Composing with a linear map
`ν : G → H¹(X; ℤ)` (`AlternatingMap.compLinearMap`) gives alternating forms on any abelian group
`G`.

These are the integral Seiberg–Witten invariants with insertions of loops, once the moduli space is
available: for a compact oriented moduli space `M` of dimension `d = r + 2m`, the class `β = μᵐ`
of a power of the point class, and the map `ν : H₁(X; ℤ) → H¹(M; ℤ)` given by slant product with
the first Chern class of the universal line, the invariant is the alternating form
`(γ₁, …, γ_r) ↦ ⟨ν(γ₁) ⌣ ⋯ ⌣ ν(γ_r) ⌣ μᵐ, [M]⟩`.

## Main definitions

* `TopCat.integralCupProd`: the iterated cup product `a₁ ⌣ ⋯ ⌣ a_r` of degree-one classes, as a
  multilinear map `H¹(X; ℤ)ʳ → Hʳ(X; ℤ)`.
* `TauCeti.HomologicalOrientation.cupInsertionForm`: the alternating form
  `(a₁, …, a_r) ↦ ⟨a₁ ⌣ ⋯ ⌣ a_r ⌣ β, f_*[N]⟩`.

## Main results

* `TopCat.integralCupProd_add_self_eq_zero`: an iterated product of degree-one classes with a
  repeated factor has order at most two.
* `TauCeti.HomologicalOrientation.cupInsertionForm_apply`: the value of the insertion form, and
  `TauCeti.HomologicalOrientation.cupInsertionForm_zero`: for `r = 0` it is `⟨β, f_*[N]⟩`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 3.2 and 3.3.
* C. Okonek and A. Teleman, *Seiberg–Witten invariants for manifolds with `b₊ = 1`, and the
  universal wall crossing formula*, Internat. J. Math. 7 (1996), 811–832.
-/

public section

noncomputable section

namespace TopCat

variable (X : TopCat.{0})

/-- **The iterated cup product of degree-one classes**, `(a₁, …, a_r) ↦ a₁ ⌣ (a₂ ⌣ ⋯ a_r)`, as
a multilinear map `H¹(X; ℤ)ʳ → Hʳ(X; ℤ)`; for `r = 0` it is the unit class. -/
def integralCupProd :
    (r : ℕ) → MultilinearMap ℤ (fun _ : Fin r ↦ X.integralCohomology 1) (X.integralCohomology r)
  | 0 => MultilinearMap.constOfIsEmpty ℤ _ X.integralCohomologyOne
  | r + 1 => MultilinearMap.mk'
    (fun v ↦ X.integralCup 1 r (r + 1) (by omega) (v 0) (integralCupProd r (Fin.tail v)))
    (fun v i x y ↦ by cases i using Fin.cases <;> simp [Ne.symm])
    (fun v i c x ↦ by cases i using Fin.cases <;> simp [Ne.symm])

/-- The empty iterated product is the unit class. -/
@[simp]
theorem integralCupProd_zero (v : Fin 0 → X.integralCohomology 1) :
    X.integralCupProd 0 v = X.integralCohomologyOne :=
  (rfl)

/-- The iterated product of `r + 1` classes is `v₀ ⌣ (v₁ ⌣ ⋯ ⌣ v_r)`. -/
theorem integralCupProd_succ (r : ℕ) (v : Fin (r + 1) → X.integralCohomology 1) :
    X.integralCupProd (r + 1) v =
      X.integralCup 1 r (r + 1) (by omega) (v 0) (X.integralCupProd r (Fin.tail v)) :=
  (rfl)

/-- If `a` occurs among `w₁, …, w_r`, then `a ⌣ w₁ ⌣ ⋯ ⌣ w_r` has order at most two. -/
theorem integralCup_integralCupProd_add_self_eq_zero (r : ℕ) {n : ℕ} (hn : 1 + r = n)
    (a : X.integralCohomology 1) (w : Fin r → X.integralCohomology 1) {k : Fin r}
    (hk : w k = a) :
    X.integralCup 1 r n hn a (X.integralCupProd r w) +
      X.integralCup 1 r n hn a (X.integralCupProd r w) = 0 := by
  induction r generalizing n with
  | zero => exact k.elim0
  | succ r ih =>
    rw [integralCupProd_succ]
    cases k using Fin.cases with
    | zero =>
      rw [← hk]
      exact X.integralCup_integralCup_self_add_self_eq_zero _ hn _ _
    | succ k =>
      rw [X.integralCup_left_anticomm, ← neg_add, ← map_add, ih (by omega) (Fin.tail w) hk,
        map_zero, neg_zero]

/-- **An iterated product with a repeated factor has order at most two**: if `v i = v j` for
`i ≠ j`, then `v₁ ⌣ ⋯ ⌣ v_r + v₁ ⌣ ⋯ ⌣ v_r = 0`. -/
theorem integralCupProd_add_self_eq_zero (r : ℕ) (v : Fin r → X.integralCohomology 1)
    {i j : Fin r}
    (hv : v i = v j) (hij : i ≠ j) : X.integralCupProd r v + X.integralCupProd r v = 0 := by
  induction r with
  | zero => exact i.elim0
  | succ r ih =>
    rw [integralCupProd_succ]
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j => exact X.integralCup_integralCupProd_add_self_eq_zero r _ _ _ hv.symm
    | succ i =>
      cases j using Fin.cases with
      | zero => exact X.integralCup_integralCupProd_add_self_eq_zero r _ _ _ hv
      | succ j =>
        rw [← map_add, ih (Fin.tail v) hv (fun h ↦ hij (congrArg Fin.succ h)), map_zero]

end TopCat

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

end HomologicalOrientation

end TauCeti
