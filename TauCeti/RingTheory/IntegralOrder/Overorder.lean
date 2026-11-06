/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IntegralOrder.Basic

/-!
# One trace-dual lattice bounds every overorder

Let `R` be an integrally closed domain with fraction field `F` and `E` a finite-dimensional
`F`-algebra whose regular trace form `(x, y) ↦ Tr_F (x * y)` is nondegenerate. Fix an `R`-order
`Λ` in `E` and an `F`-basis `e` of `E` inside `Λ`, and let `r = det (Tr_F (e i * e j))` be its
Gram determinant, which is nonzero. Every element of an overorder `Γ ⊇ Λ` is integral over `R`, so
the regular traces `Tr_F (x * e j)` for `x ∈ Γ` lie in `R`; Cramer's rule in the fixed Gram matrix
then puts `r • x` in the `R`-span of `e`. Hence every overorder of `Λ` lies in the single module
`r⁻¹ • span R e`, which depends on `Λ` and `e` but not on `Γ`.

Over a noetherian `R` this module is noetherian, so the overorders of `Λ` satisfy the ascending
chain condition. This is the finiteness input for the existence of maximal orders containing a given
order.

## Main results

* `TauCeti.IntegralOrder.det_smul_mem_span`: if `Γ` is an `R`-subalgebra of integral elements
  containing the `F`-basis `e`, then `r • x ∈ span R e` for every `x ∈ Γ`.
* `TauCeti.IntegralOrder.toSubmodule_le_inv_det_smul_span`: for a nondegenerate regular trace form,
  every such `Γ` lies in `r⁻¹ • span R e`.
* `TauCeti.IntegralOrder.IsOrder.wellFoundedGT_overorder`: over a noetherian integrally closed `R`,
  the orders containing a given order satisfy the ascending chain condition.

## References

* J. Voight, *Quaternion algebras*, proof of Lemma 10.3.7 and paragraph 10.4.2; Voight uses the
  reduced trace of a separable algebra, and here the regular trace is used instead.
-/

public section

open Module Submodule Pointwise

namespace TauCeti.IntegralOrder

variable {R F E : Type*} [CommRing R] [Field F] [Ring E]
  [Algebra R F] [IsFractionRing R F] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [FiniteDimensional F E] [IsIntegrallyClosed R]

/-- **Cramer's bound for subalgebras of integral elements.** Let `e` be an `F`-basis of `E` lying in
an `R`-subalgebra `Γ` all of whose elements are integral over the integrally closed domain `R`, and
let `r = det (Tr_F (e i * e j))` be the Gram determinant of the regular trace form. Then `r • x`
lies in the `R`-span of `e` for every `x ∈ Γ`. -/
theorem det_smul_mem_span {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι F E)
    {Γ : Subalgebra R E} (he : ∀ i, e i ∈ Γ) (hint : ∀ x ∈ Γ, IsIntegral R x) {x : E}
    (hx : x ∈ Γ) :
    (LinearMap.BilinForm.toMatrix e (Algebra.regularTraceForm F E)).det • x ∈
      span R (Set.range e) := by
  have hΓ := toSubmodule_le_dualSubmodule_regularTraceForm (F := F) hint
  refine (Algebra.regularTraceForm F E).det_toMatrix_smul_mem_span e
    (fun i j => hΓ (he i) _ (he j)) ?_
  exact (Algebra.regularTraceForm F E).dualSubmodule_anti
    (span_le.2 <| Set.range_subset_iff.2 he) (hΓ hx)

/-- **One trace-dual lattice bounds every overorder.** Let `R` be integrally closed, let the regular
trace form of `E` be nondegenerate, and let `e` be an `F`-basis of `E` with Gram determinant
`r = det (Tr_F (e i * e j))`. Every `R`-subalgebra `Γ` of integral elements containing `e` lies in
`r⁻¹ • span R e`. Taking `e` inside an order `Λ`, this applies to every overorder `Γ ⊇ Λ`, and the
bound does not depend on `Γ`. -/
theorem toSubmodule_le_inv_det_smul_span (hB : (Algebra.regularTraceForm F E).Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι F E) {Γ : Subalgebra R E}
    (he : ∀ i, e i ∈ Γ) (hint : ∀ x ∈ Γ, IsIntegral R x) :
    Subalgebra.toSubmodule Γ ≤
      (LinearMap.BilinForm.toMatrix e (Algebra.regularTraceForm F E)).det⁻¹ •
        span R (Set.range e) := fun x hx => by
  have hr := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero e).1 hB
  exact mem_smul_pointwise_iff_exists _ _ _ |>.2
    ⟨_, det_smul_mem_span e he hint hx, by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]⟩

/-- **Ascending chain condition for overorders.** Let `R` be an integrally closed noetherian domain
and let the regular trace form of `E` be nondegenerate. For an `R`-order `Λ` in `E`, the `R`-orders
in `E` containing `Λ` satisfy the ascending chain condition: they all lie in one finitely generated
`R`-module, the trace-dual lattice of an `F`-basis of `E` inside `Λ`. -/
theorem IsOrder.wellFoundedGT_overorder [IsNoetherianRing R]
    (hB : (Algebra.regularTraceForm F E).Nondegenerate) {Λ : Subalgebra R E}
    (hΛ : IsOrder F Λ) : WellFoundedGT {Γ : Subalgebra R E // Λ ≤ Γ ∧ IsOrder F Γ} := by
  classical
  -- every overorder lies in the trace-dual lattice `M` of a basis `e ⊆ Λ`, which is noetherian
  let e := Basis.ofSpan hΛ.span_eq_top.ge
  have he : ∀ i, e i ∈ Λ := fun i => Basis.ofSpan_subset _ ⟨i, rfl⟩
  let M := span R (Set.range ((Algebra.regularTraceForm F E).dualBasis hB e))
  have : IsNoetherian R M := isNoetherian_of_fg_of_noetherian M (fg_span (Set.finite_range _))
  have hle (Γ : {Γ : Subalgebra R E // Λ ≤ Γ ∧ IsOrder F Γ}) : Subalgebra.toSubmodule Γ.1 ≤ M :=
    toSubmodule_le_span_dualBasis hB e (fun i => Γ.2.1 (he i)) fun _ => Γ.2.2.isIntegral
  -- so the overorders embed strictly monotonically into the submodules of `M`
  let f (Γ : {Γ : Subalgebra R E // Λ ≤ Γ ∧ IsOrder F Γ}) : Submodule R M :=
    (Subalgebra.toSubmodule Γ.1).comap M.subtype
  have hf : StrictMono f := by
    refine Monotone.strictMono_of_injective
      (fun _ _ h => comap_mono (Subalgebra.toSubmodule.monotone h)) fun Γ₁ Γ₂ h => ?_
    have h' := congrArg (map M.subtype) h
    simp only [f, map_comap_subtype, inf_eq_right.2 (hle Γ₁), inf_eq_right.2 (hle Γ₂)] at h'
    exact Subtype.ext (Subalgebra.toSubmodule_injective h')
  exact hf.wellFoundedGT

end TauCeti.IntegralOrder
