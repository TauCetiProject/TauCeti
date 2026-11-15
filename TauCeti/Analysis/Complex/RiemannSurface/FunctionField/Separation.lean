/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField
import Mathlib.Algebra.Module.Submodule.Union

/-!
# Separating finitely many points by one meromorphic function

Let `X` be a connected Riemann surface and `s` a finite set of points of `X`. If every two
distinct points of `s` are separated by some meromorphic function, then a single meromorphic
function separates all of them at once, and it can be chosen without poles on `s`
(`TauCeti.RiemannSurface.MeromorphicFunction.exists_forall_ne_infty_and_injOn`).

The pairwise separators may have poles on `s`. Each is first replaced by `(g - c)⁻¹` for a
constant `c` that `g` does not take on `s`; this has no poles on `s` and still separates the same
two points. The meromorphic functions without poles on `s` form a `ℂ`-subspace on which evaluation
at a point of `s` is linear, and each pair `x ≠ y` of points of `s` gives the nonzero linear form
`f ↦ f(x) - f(y)` on it. A vector space over an infinite field is not a finite union of proper
subspaces (`Module.Dual.exists_forall_ne_zero_of_forall_exists`), so a generic linear combination
of the separators avoids the kernels of all these forms at once.

This is the fibre-separation step of the degree theorem for `M(X) / ℂ(t)`: a meromorphic function
taking `n` distinct values on an unbranched fibre of a degree-`n` map to the sphere has degree `n`
over `ℂ(t)`.

## Main results

* `TauCeti.RiemannSurface.MeromorphicFunction.exists_forall_ne_infty_and_injOn`: finitely many
  pairwise separated points are separated by one meromorphic function without poles at them.
-/

public noncomputable section

open OnePoint Set

open scoped Manifold

namespace TauCeti.RiemannSurface.MeromorphicFunction

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X] {s : Set X}

/-- A separator of two points of a finite set `s` can be replaced by one without poles on `s`:
`(g - c)⁻¹`, for a constant `c` that `g` does not take on `s`. -/
private theorem exists_forall_ne_infty_and_ne (hs : s.Finite) {x y : X} (hx : x ∈ s)
    (hy : y ∈ s) {g : MeromorphicFunction X} (hg : g x ≠ g y) :
    ∃ h : MeromorphicFunction X, (∀ z ∈ s, h z ≠ ∞) ∧ h x ≠ h y := by
  obtain ⟨c, hc⟩ := ((hs.image g).preimage coe_injective.injOn).exists_notMem
  have hgc (z : X) (hz : z ∈ s) : g z ≠ c := fun h ↦ hc ⟨z, hz, h⟩
  set k := g - algebraMap ℂ (MeromorphicFunction X) c
  -- At a pole of `g`, the inverse `k⁻¹` vanishes; elsewhere on `s` it is `(g - c)⁻¹`, nonzero.
  have hpole (z : X) (hz : g z = ∞) : k⁻¹ z = ((0 : ℂ) : OnePoint ℂ) := by
    refine inv_apply_of_eq_infty (by_contra fun hk ↦ ?_)
    have : g = k + algebraMap ℂ (MeromorphicFunction X) c := by simp [k]
    rw [this, add_apply hk (by simp)] at hz
    exact OnePoint.coe_ne_infty _ hz
  have hfin (z : X) (hz : z ∈ s) (a : ℂ) (ha : g z = a) : k⁻¹ z = ↑(a - c)⁻¹ :=
    inv_apply_of_eq_coe (sub_apply_of_eq_coe ha (by simp))
      (sub_ne_zero.2 fun h ↦ hgc z hz (by rw [ha, h]))
  refine ⟨k⁻¹, fun z hz ↦ ?_, ?_⟩
  · by_cases hgz : g z = ∞
    · simp [hpole z hgz]
    · obtain ⟨a, ha⟩ := ne_infty_iff_exists.1 hgz
      simp [hfin z hz a ha.symm]
  · by_cases hgx : g x = ∞
    · obtain ⟨b, hb⟩ := ne_infty_iff_exists.1 (hgx ▸ hg.symm)
      rw [hpole x hgx, hfin y hy b hb.symm, Ne, coe_eq_coe, eq_comm, inv_eq_zero, sub_eq_zero]
      exact fun h ↦ hgc y hy (by rw [← hb, h])
    obtain ⟨a, ha⟩ := ne_infty_iff_exists.1 hgx
    by_cases hgy : g y = ∞
    · rw [hfin x hx a ha.symm, hpole y hgy, Ne, coe_eq_coe, inv_eq_zero, sub_eq_zero]
      exact fun h ↦ hgc x hx (by rw [← ha, h])
    obtain ⟨b, hb⟩ := ne_infty_iff_exists.1 hgy
    rw [hfin x hx a ha.symm, hfin y hy b hb.symm, Ne, coe_eq_coe, inv_inj, sub_left_inj]
    exact fun h ↦ hg (by rw [← ha, ← hb, h])

/-- The meromorphic functions without poles on `s`, as a `ℂ`-subspace. -/
private def finiteOn (s : Set X) : Submodule ℂ (MeromorphicFunction X) where
  carrier := {f | ∀ x ∈ s, f x ≠ ∞}
  add_mem' {f g} hf hg x hx := by simp [add_apply (hf x hx) (hg x hx)]
  zero_mem' x _ := by simp
  smul_mem' c f hf x hx := by
    rw [Algebra.smul_def, mul_apply (f := algebraMap ℂ _ c) (by simp) (hf x hx)]
    exact OnePoint.coe_ne_infty _

/-- Evaluation at a point of `s`, as a linear form on the meromorphic functions without poles on
`s`. -/
private def evalFiniteOn {x : X} (hx : x ∈ s) : Module.Dual ℂ (finiteOn s) where
  toFun f := (f : MeromorphicFunction X).finitePart x
  map_add' f g := finitePart_of_eq_coe (add_apply (f.2 x hx) (g.2 x hx))
  map_smul' c f := by
    refine finitePart_of_eq_coe ?_
    rw [SetLike.val_smul, Algebra.smul_def, mul_apply (f := algebraMap ℂ _ c) (by simp) (f.2 x hx)]
    simp

private theorem evalFiniteOn_apply {x : X} (hx : x ∈ s) (f : finiteOn s) :
    evalFiniteOn hx f = (f : MeromorphicFunction X).finitePart x :=
  rfl

/-- **Separating finitely many points by one meromorphic function.** On a connected Riemann
surface, if every two distinct points of a finite set `s` are separated by some meromorphic
function, then a single meromorphic function without poles on `s` takes pairwise distinct values
at the points of `s`. -/
theorem exists_forall_ne_infty_and_injOn (hs : s.Finite)
    (hsep : s.Pairwise fun x y ↦ ∃ g : MeromorphicFunction X, g x ≠ g y) :
    ∃ f : MeromorphicFunction X, (∀ x ∈ s, f x ≠ ∞) ∧ s.InjOn f := by
  let ι := {q : X × X // q.1 ∈ s ∧ q.2 ∈ s ∧ q.1 ≠ q.2}
  have := (hs.prod hs).to_subtype
  have : Finite ι := Finite.of_injective (fun q : ι ↦ (⟨q.1, q.2.1, q.2.2.1⟩ : ↥(s ×ˢ s)))
    fun _ _ h ↦ Subtype.ext (congrArg Subtype.val h :)
  -- The linear form `f ↦ f(x) - f(y)` attached to a pair `x ≠ y` of points of `s`.
  let D (q : ι) : Module.Dual ℂ (finiteOn s) := evalFiniteOn q.2.1 - evalFiniteOn q.2.2.1
  obtain ⟨⟨f, hf⟩, hD⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists D fun q ↦ by
    obtain ⟨g, hg⟩ := hsep q.2.1 q.2.2.1 q.2.2.2
    obtain ⟨h, hh, hxy⟩ := exists_forall_ne_infty_and_ne hs q.2.1 q.2.2.1 hg
    refine ⟨⟨h, hh⟩, sub_ne_zero.2 fun he ↦ hxy ?_⟩
    rw [← coe_finitePart (hh _ q.2.1), ← coe_finitePart (hh _ q.2.2.1)]
    exact congrArg _ he
  refine ⟨f, hf, fun x hx y hy hxy ↦ by_contra fun hne ↦ hD ⟨(x, y), hx, hy, hne⟩ ?_⟩
  rw [LinearMap.sub_apply, evalFiniteOn_apply, evalFiniteOn_apply, finitePart_def, finitePart_def,
    hxy, sub_self]

end TauCeti.RiemannSurface.MeromorphicFunction
