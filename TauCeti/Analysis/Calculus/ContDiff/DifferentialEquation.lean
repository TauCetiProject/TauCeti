/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Regularity of total differential equations

A differentiable solution of `Df x = V (x, f x)` gains one derivative over the regularity
of the joint right-hand side. For an equation affine in the first derivative, a solution
with differentiable `f` and `Df` is `C^(n+2)` when the coefficients are `C^n` on an open set.
Both finite order and smooth coefficients are covered, over arbitrary nontrivially normed
fields and normed spaces.

## References

* The coordinate bootstrap in
  `PoincareMT.LeviCivitaData.contDiffOn_of_C2_hessian_eq_smooth_mul_metric` in the public
  formalizations https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
-/

public section

open Set
open scoped ContDiff

namespace TauCeti
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A solution of a `C^n` total differential equation is `C^(n+1)` on an arbitrary set.
The coefficients need only be regular along a set containing its graph. -/
theorem contDiffOn_succ_of_hasFDerivWithinAt_comp {n : ℕ∞} {U : Set E}
    {f : E → F} {S : Set (E × F)}
    {V : E × F → E →L[𝕜] F} (hV : ContDiffOn 𝕜 n V S)
    (hgraph : MapsTo (fun x ↦ (x, f x)) U S)
    (hf : ∀ x ∈ U, HasFDerivWithinAt f (V (x, f x)) U x) :
    ContDiffOn 𝕜 (n + 1) f U := by
  have key (m : ℕ) (hm : m ≤ n + 1) : ContDiffOn 𝕜 m f U := by
    induction m with
    | zero => exact contDiffOn_zero.mpr fun x hx ↦ (hf x hx).continuousWithinAt
    | succ m ih =>
      have hmn : (m : ℕ∞) ≤ n := by simpa using hm
      rw [Nat.cast_add, Nat.cast_one]
      intro x hx
      rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt (by simp), insert_eq_of_mem hx]
      exact ⟨U, self_mem_nhdsWithin, by simp, fun y ↦ V (y, f y), hf,
        ((hV.of_le (mod_cast hmn)).comp
          (contDiffOn_id.prodMk (ih (hmn.trans le_self_add))) hgraph) x hx⟩
  exact_mod_cast contDiffOn_iff_forall_nat_le.mpr key

/-- Prescribed second derivatives with a `C^n` affine dependence on `Df` give
`C^(n+2)` regularity. -/
theorem contDiffOn_add_two_of_fderiv_fderiv_eq {n : ℕ∞} {U : Set E} (hU : IsOpen U)
    {f : E → F} {A : E → E →L[𝕜] E →L[𝕜] F} {Γ : E → E →L[𝕜] E →L[𝕜] E}
    (hf : DifferentiableOn 𝕜 f U) (hdf : DifferentiableOn 𝕜 (fderiv 𝕜 f) U)
    (hA : ContDiffOn 𝕜 n A U) (hΓ : ContDiffOn 𝕜 n Γ U)
    (heq : ∀ x ∈ U, fderiv 𝕜 (fderiv 𝕜 f) x =
      A x + (ContinuousLinearMap.compL 𝕜 E E F (fderiv 𝕜 f x)).comp (Γ x)) :
    ContDiffOn 𝕜 (n + 2) f U := by
  let V (p : E × (E →L[𝕜] F)) : E →L[𝕜] E →L[𝕜] F :=
    A p.1 + (ContinuousLinearMap.compL 𝕜 E E F p.2).comp (Γ p.1)
  have hV : ContDiffOn 𝕜 n V (U ×ˢ (univ : Set (E →L[𝕜] F))) := by
    have hA' : ContDiffOn 𝕜 n (fun p : E × (E →L[𝕜] F) ↦ A p.1)
        (U ×ˢ (univ : Set (E →L[𝕜] F))) :=
      hA.comp contDiffOn_fst (fun _ hx ↦ hx.1)
    have hΓ' : ContDiffOn 𝕜 n (fun p : E × (E →L[𝕜] F) ↦ Γ p.1)
        (U ×ˢ (univ : Set (E →L[𝕜] F))) :=
      hΓ.comp contDiffOn_fst (fun _ hx ↦ hx.1)
    exact hA'.add ((contDiffOn_const.clm_apply contDiffOn_snd).clm_comp hΓ')
  have hfd := contDiffOn_succ_of_hasFDerivWithinAt_comp (f := fderiv 𝕜 f) hV
    (fun _ hx ↦ ⟨hx, mem_univ _⟩) fun x hx ↦ by
      -- Express the graph coefficient using the local definition of the affine right-hand side.
      change HasFDerivWithinAt (fderiv 𝕜 f)
        (A x + (ContinuousLinearMap.compL 𝕜 E E F (fderiv 𝕜 f x)).comp (Γ x)) U x
      rw [← heq x hx]
      exact ((hdf x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt
  have hreg : ContDiffOn 𝕜 ((n : ℕ∞ω) + 1 + 1) f U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hU).2 ⟨hf, by simp, hfd⟩
  simpa only [add_assoc, one_add_one_eq_two] using hreg

end TauCeti
