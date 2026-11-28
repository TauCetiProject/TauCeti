/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

import TauCeti.LinearAlgebra.Finsupp.LinearCombination
import TauCeti.LinearAlgebra.Matrix.Charpoly.Family

/-!
# Trace ideals and common Ribet elements

Let `O` be a commutative ring, `L` a commutative `O`-algebra, `J` and `Y` types, and
`u_x : G → M_σ(L)` (`x ∈ Y`) a family of maps, typically matrix representations of a group `G`
read over `L`. Ribet's method to first order works with families, indexed by `x ∈ Y`, of
polynomials over `L` in variables `X_j` (`j ∈ J`): an `O`-subalgebra `S` of `Y → L[X_j]` and an
`S`-submodule `𝒥`.

* `𝒥` is a **trace ideal** (`TauCeti.IsTraceIdeal`) for `p ∈ O`, elements `τ_i, φ_i ∈ G`, indices
  `k(i) ∈ J` and polynomials `ε_j ∈ O[X]` if `S` contains the constant families `X_j` and the
  coefficients of the characteristic polynomials of the `u_x(g)`, and `𝒥` contains the families
  `p · tr u_x(g)` and
  `tr((u_x(τ_i) - 1) u_x(g)) - X_{k(i)} · tr(((X - 1) ε_{k(i)})(u_x(φ_i)) u_x(g))`: the traces
  of `p` and of the ties `τ_i - 1 - X_{k(i)} ε_{k(i)}(φ_i) (φ_i - 1)` against every group
  element.
* For functions `β_i : Y → L`, a set `𝓧 ⊆ Y`, a point `π ∈ 𝓧` and `c ∈ L`, an element `f ∈ S` is a
  **common Ribet element** (`TauCeti.IsCommonRibetElement`) if the constant families `β_i` lie in
  `S` and vanish on `𝓧`, every `f · β_i` lies in `𝒥`, `f` has at every `x ∈ 𝓧` coefficient `0` at
  every monomial properly dividing `∏_j X_j`, and `f(π)` has coefficient `c` at `∏_j X_j`.

The families `β` of interest are the determinants `x ↦ det (∑_g ω_g (u_x(g) - 1))`. They lie in
`S` as soon as `S` contains the coefficients of the characteristic polynomials of the `u_x(g)`
(`TauCeti.C_det_linearCombination_sub_one_mem`, in
`TauCeti.LinearAlgebra.Matrix.Charpoly.Family`).

## Main definitions

* `TauCeti.IsTraceIdeal 𝒥 u p τ φ k ε`: `𝒥` is a trace ideal.
* `TauCeti.IsCommonRibetElement 𝒥 β π c f`: `f` is a common Ribet element for `β` at `π` with
  coefficient `c`.

## Main results

* `TauCeti.IsTraceIdeal.C_smul_trace_linearCombination_mem`,
  `TauCeti.IsTraceIdeal.tie_linearCombination_mem`: a trace ideal contains the traces of `p` and
  of the ties against every `O`-linear combination of the `u_x(g)`.
* `TauCeti.isCommonRibetElement_det`: for the determinant families, the conditions in `S` and on
  `𝓧` hold as soon as `S` contains the characteristic coefficients and every `u_x`, `x ∈ 𝓧`, fixes
  one basis vector; only the conditions on `f` remain.
* `TauCeti.IsCommonRibetElement.add`, `TauCeti.IsCommonRibetElement.smul`: common Ribet elements
  for `β` at `π` add, and scale, with their coefficients.

## References

* K. A. Ribet, *A modular construction of unramified p-extensions of Q(μ_p)*, Invent. Math. 34
  (1976), 151–162.
* J. Bellaïche and G. Chenevier, *Families of Galois representations and Selmer groups*,
  Astérisque 324 (2009), Chapter 1.
* The definitions follow `New.Selmer.IsTraceIdeal` and `New.Selmer.IsCommonRibetElement` in the
  file `src/New/Congruences/FirstOrder/FittingBlock.lean` of grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Matrix

namespace TauCeti

section Families

variable {O L Y J G σ : Type*} [CommRing O] [CommRing L] [Algebra O L] [Fintype σ] [DecidableEq σ]
  {S : Subalgebra O (Y → MvPolynomial J L)}

/-- The `S`-submodule `𝒥` of the families `Y → L[X_j]` is a **trace ideal** for the matrices
`u x g`, `p ∈ O`, the elements `τ i`, `φ i` of `G`, the indices `k i` and the polynomials
`ε j ∈ O[X]`: the algebra `S` contains the constant families `X j` and the families of the
coefficients of the characteristic polynomials of the `u x g`, and `𝒥` contains the families
`x ↦ p • tr (u x g)` and
`x ↦ tr ((u x (τ i) - 1) * u x g) - X (k i) * tr (((X - 1) * ε (k i)) (u x (φ i)) * u x g)`. -/
structure IsTraceIdeal (𝒥 : Submodule S (Y → MvPolynomial J L)) {K : Type*}
    (u : Y → G → Matrix σ σ L) (p : O) (τ φ : K → G) (k : K → J) (ε : J → Polynomial O) :
    Prop where
  /-- The algebra `S` contains the constant families `X j`. -/
  X_mem (j : J) : (fun _ : Y ↦ MvPolynomial.X j) ∈ S
  /-- The algebra `S` contains the families of the coefficients of the characteristic
  polynomials of the `u x g`. -/
  C_charpoly_coeff_mem (g : G) (n : ℕ) : (fun x ↦ MvPolynomial.C ((u x g).charpoly.coeff n)) ∈ S
  /-- The module `𝒥` contains the families of the traces of `p • u x g`. -/
  C_smul_trace_mem (g : G) : (fun x ↦ MvPolynomial.C (p • (u x g).trace)) ∈ 𝒥
  /-- The module `𝒥` contains the families of the traces of the ties against `u x g`. -/
  tie_mem (g : G) (i : K) :
    (fun x ↦ MvPolynomial.C ((u x (τ i) - 1) * u x g).trace - MvPolynomial.X (k i) *
      MvPolynomial.C ((Polynomial.aeval (u x (φ i)) ((Polynomial.X - 1) * ε (k i)) *
        u x g).trace)) ∈ 𝒥

namespace IsTraceIdeal

variable {𝒥 𝒥' : Submodule S (Y → MvPolynomial J L)} {K : Type*} {u : Y → G → Matrix σ σ L}
  {p : O} {τ φ : K → G} {k : K → J} {ε : J → Polynomial O}

/-- A submodule containing a trace ideal is a trace ideal. -/
theorem mono (h : IsTraceIdeal 𝒥 u p τ φ k ε) (h𝒥 : 𝒥 ≤ 𝒥') : IsTraceIdeal 𝒥' u p τ φ k ε where
  X_mem := h.X_mem
  C_charpoly_coeff_mem := h.C_charpoly_coeff_mem
  C_smul_trace_mem g := h𝒥 (h.C_smul_trace_mem g)
  tie_mem g i := h𝒥 (h.tie_mem g i)

/-- A trace ideal contains the families of the traces of `p • ∑_g θ_g • u x g`, for every
finitely supported `θ`. -/
theorem C_smul_trace_linearCombination_mem (h : IsTraceIdeal 𝒥 u p τ φ k ε) (θ : G →₀ O) :
    (fun x ↦ MvPolynomial.C (p • (Finsupp.linearCombination O (u x) θ).trace)) ∈ 𝒥 := by
  let F (_ : Y) : Matrix σ σ L →ₗ[O] MvPolynomial J L :=
    (IsScalarTower.toAlgHom O L (MvPolynomial J L)).toLinearMap ∘ₗ
      (p • Matrix.traceLinearMap σ O L)
  have hF (x : Y) (M : Matrix σ σ L) : F x M = MvPolynomial.C (p • M.trace) := by
    simp [F, MvPolynomial.algebraMap_eq]
  convert 𝒥.linearCombination_mem (v := fun g x ↦ F x (u x g))
    (fun g ↦ by simpa [hF] using h.C_smul_trace_mem g) θ using 1
  funext x
  rw [Finsupp.linearCombination_pi_apply, ← hF x]
  exact Finsupp.apply_linearCombination O (F x) (u x) θ

/-- A trace ideal contains the families of the traces of the ties against every
`∑_g θ_g • u x g`, for finitely supported `θ`. -/
theorem tie_linearCombination_mem (h : IsTraceIdeal 𝒥 u p τ φ k ε) (θ : G →₀ O) (i : K) :
    (fun x ↦ MvPolynomial.C ((u x (τ i) - 1) * Finsupp.linearCombination O (u x) θ).trace -
      MvPolynomial.X (k i) * MvPolynomial.C ((Polynomial.aeval (u x (φ i))
        ((Polynomial.X - 1) * ε (k i)) * Finsupp.linearCombination O (u x) θ).trace)) ∈ 𝒥 := by
  let F (x : Y) : Matrix σ σ L →ₗ[O] MvPolynomial J L :=
    (IsScalarTower.toAlgHom O L (MvPolynomial J L)).toLinearMap ∘ₗ
        (Matrix.traceLinearMap σ O L ∘ₗ LinearMap.mulLeft O (u x (τ i) - 1)) -
      (MvPolynomial.X (k i) : MvPolynomial J L) •
        ((IsScalarTower.toAlgHom O L (MvPolynomial J L)).toLinearMap ∘ₗ
          (Matrix.traceLinearMap σ O L ∘ₗ LinearMap.mulLeft O
            (Polynomial.aeval (u x (φ i)) ((Polynomial.X - 1) * ε (k i)))))
  have hF (x : Y) (M : Matrix σ σ L) : F x M = MvPolynomial.C ((u x (τ i) - 1) * M).trace -
      MvPolynomial.X (k i) * MvPolynomial.C ((Polynomial.aeval (u x (φ i))
        ((Polynomial.X - 1) * ε (k i)) * M).trace) := by
    simp [F, MvPolynomial.algebraMap_eq, mul_assoc]
  convert 𝒥.linearCombination_mem (v := fun g x ↦ F x (u x g))
    (fun g ↦ by simpa [hF] using h.tie_mem g i) θ using 1
  funext x
  rw [Finsupp.linearCombination_pi_apply, ← hF x]
  exact Finsupp.apply_linearCombination O (F x) (u x) θ

end IsTraceIdeal

/-- `f ∈ S` is a **common Ribet element** for the functions `β i : Y → L` at the point `π` of
`𝓧 ⊆ Y`, with coefficient `c`: the constant families `β i` lie in `S` and vanish on `𝓧`, every
`f * β i` lies in `𝒥`, at every `x ∈ 𝓧` the polynomial `f x` has coefficient `0` at every monomial
properly dividing `∏ j, X j`, and `f π` has coefficient `c` at `∏ j, X j`. -/
structure IsCommonRibetElement [Fintype J] (𝒥 : Submodule S (Y → MvPolynomial J L)) {I : Type*}
    (β : I → Y → L) {𝓧 : Set Y} (π : 𝓧) (c : L) (f : S) : Prop where
  /-- The constant families `β i` lie in `S`. -/
  C_mem (i : I) : (fun x ↦ MvPolynomial.C (β i x)) ∈ S
  /-- The functions `β i` vanish on `𝓧`. -/
  eq_zero (i : I) (x : 𝓧) : β i x = 0
  /-- The element `f` multiplies every `β i` into `𝒥`. -/
  mul_mem (i : I) : (f : Y → MvPolynomial J L) * (fun x ↦ MvPolynomial.C (β i x)) ∈ 𝒥
  /-- On `𝓧`, `f` has no monomial properly dividing `∏ j, X j`. -/
  coeff_eq_zero (x : 𝓧) (d : J →₀ ℕ) (hd : d < ∑ j, Finsupp.single j 1) :
    ((f : Y → MvPolynomial J L) x).coeff d = 0
  /-- The coefficient of `∏ j, X j` in `f π` is `c`. -/
  coeff_eq : ((f : Y → MvPolynomial J L) π).coeff (∑ j, Finsupp.single j 1) = c

namespace IsCommonRibetElement

variable [Fintype J] {𝒥 𝒥' : Submodule S (Y → MvPolynomial J L)} {I : Type*} {β : I → Y → L}
  {𝓧 : Set Y} {π : 𝓧} {c c' : L} {f f' : S}

/-- A common Ribet element for `𝒥` is one for every larger submodule. -/
theorem mono (h : IsCommonRibetElement 𝒥 β π c f) (h𝒥 : 𝒥 ≤ 𝒥') :
    IsCommonRibetElement 𝒥' β π c f where
  C_mem := h.C_mem
  eq_zero := h.eq_zero
  mul_mem i := h𝒥 (h.mul_mem i)
  coeff_eq_zero := h.coeff_eq_zero
  coeff_eq := h.coeff_eq

/-- A common Ribet element for `β` is one for every reindexed family `β ∘ e`. -/
theorem comp (h : IsCommonRibetElement 𝒥 β π c f) {I' : Type*} (e : I' → I) :
    IsCommonRibetElement 𝒥 (β ∘ e) π c f where
  C_mem i := h.C_mem (e i)
  eq_zero i := h.eq_zero (e i)
  mul_mem i := h.mul_mem (e i)
  coeff_eq_zero := h.coeff_eq_zero
  coeff_eq := h.coeff_eq

/-- The sum of two common Ribet elements for `β` at `π` is one, with the sum of the
coefficients. -/
theorem add (h : IsCommonRibetElement 𝒥 β π c f) (h' : IsCommonRibetElement 𝒥 β π c' f') :
    IsCommonRibetElement 𝒥 β π (c + c') (f + f') where
  C_mem := h.C_mem
  eq_zero := h.eq_zero
  mul_mem i := by simpa [add_mul] using 𝒥.add_mem (h.mul_mem i) (h'.mul_mem i)
  coeff_eq_zero x d hd := by simp [h.coeff_eq_zero x d hd, h'.coeff_eq_zero x d hd]
  coeff_eq := by simp [h.coeff_eq, h'.coeff_eq]

/-- A multiple `r • f`, `r ∈ O`, of a common Ribet element `f` is one, with coefficient
`r • c`. -/
theorem smul (h : IsCommonRibetElement 𝒥 β π c f) (r : O) :
    IsCommonRibetElement 𝒥 β π (r • c) (r • f) where
  C_mem := h.C_mem
  eq_zero := h.eq_zero
  mul_mem i := by simpa [smul_mul_assoc] using 𝒥.smul_of_tower_mem r (h.mul_mem i)
  coeff_eq_zero x d hd := by simp [h.coeff_eq_zero x d hd]
  coeff_eq := by simp [h.coeff_eq]

end IsCommonRibetElement

/-- **Common Ribet elements for determinants.** Let `S` contain the families of the
coefficients of the characteristic polynomials of the `u x g`, and let every `u x`, `x ∈ 𝓧`, fix
the basis vector `e_{j₀}`, so that the column `j₀` of every `u x g - 1` vanishes. Then an `f ∈ S`
that multiplies every family `x ↦ det (∑_g θ_g (u x g - 1))` into `𝒥`, has at every `x ∈ 𝓧` no
monomial properly dividing `∏ j, X j`, and has coefficient `c` at `∏ j, X j` in `f π`, is a common
Ribet element for these determinants. -/
theorem isCommonRibetElement_det [Fintype J] [Monoid G] {𝒥 : Submodule S (Y → MvPolynomial J L)}
    (u : Y → G →* Matrix σ σ L)
    (hS : ∀ g n, (fun x ↦ MvPolynomial.C ((u x g).charpoly.coeff n)) ∈ S) {𝓧 : Set Y}
    {j₀ : σ} (hfix : ∀ x ∈ 𝓧, ∀ g i, u x g i j₀ = (1 : Matrix σ σ L) i j₀) (π : 𝓧) {c : L}
    {f : S}
    (hmul : ∀ θ : G →₀ O, (f : Y → MvPolynomial J L) *
      (fun x ↦ MvPolynomial.C (Finsupp.linearCombination O (fun g ↦ u x g - 1) θ).det) ∈ 𝒥)
    (hcoeff : ∀ x : 𝓧, ∀ d < ∑ j, Finsupp.single j 1,
      ((f : Y → MvPolynomial J L) x).coeff d = 0)
    (hπ : ((f : Y → MvPolynomial J L) π).coeff (∑ j, Finsupp.single j 1) = c) :
    IsCommonRibetElement 𝒥
      (fun (θ : G →₀ O) x ↦ (Finsupp.linearCombination O (fun g ↦ u x g - 1) θ).det) π c f where
  C_mem θ := C_det_linearCombination_sub_one_mem u hS θ
  eq_zero θ x := by
    refine det_eq_zero_of_column_eq_zero j₀ fun i ↦ ?_
    simp [Finsupp.linearCombination_apply, Finsupp.sum, Matrix.sum_apply,
      hfix x.val x.property _ i]
  mul_mem := hmul
  coeff_eq_zero := hcoeff
  coeff_eq := hπ

end Families

end TauCeti
