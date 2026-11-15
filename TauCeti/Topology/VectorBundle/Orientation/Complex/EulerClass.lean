/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Complex.Basic
public import TauCeti.Topology.VectorBundle.Orientation.EulerClass

/-!
# The Euler class of the underlying real bundle of a complex vector bundle

Let `E → B` be a complex vector bundle whose model fibre `F` has complex dimension `r + 1`. Its
underlying real bundle `E_ℝ` has rank `2r + 2` and carries the canonical orientation
`TauCeti.VectorBundleOrientation.complex F E`, in which every fibre is oriented by
`(v₁, i v₁, …, v_{r+1}, i v_{r+1})` for any complex basis `(v₁, …, v_{r+1})`. The Euler class of
this oriented real bundle is the class `e(E_ℝ) ∈ H²ʳ⁺²(B; ℤ)`
(`TauCeti.complexEulerClass`). The canonical orientation is indexed by
`Fin (2 * finrank ℂ F)`, while the Euler class of an oriented bundle is defined for orientations
indexed by `Fin (n + 1)`, so the definition reindexes along `2 (r + 1) = (2r + 1) + 1`
(`TauCeti.VectorBundleOrientation.reindex`).

This is the class that the top Chern class `c_{r+1}(E)` is to be compared with (`c_r = e(E_ℝ)` in
rank `r`); for a complex line bundle it is the class `e(L_ℝ) ∈ H²(B; ℤ)` that `c₁(L)` is compared
with. Since the canonical orientation is natural and constant on trivial bundles, the class
inherits the laws of the Euler class of an oriented bundle:

* it is natural under pullback (`TauCeti.complexEulerClass_pullback`);
* it vanishes when the bundle has a nowhere-zero continuous section
  (`TauCeti.complexEulerClass_eq_zero_of_forall_ne_zero`), in particular for the trivial bundle
  `B × F` (`TauCeti.complexEulerClass_trivial`).

Integral coefficients are `ULift ℤ`, as for the Euler class of an oriented bundle.

## Main definitions

* `TauCeti.complexEulerClass`: the Euler class of the underlying real bundle of a complex vector
  bundle, with its canonical orientation.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the canonical orientation of a complex vector bundle and the top Chern
  class as its Euler class).
-/

public section

noncomputable section

open Bundle Module

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B]
  (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, Module ℂ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℂ F E]
  {r : ℕ} (hF : finrank ℂ F = r + 1)

local instance instVectorBundleRealComplexEulerClass : VectorBundle ℝ F E :=
  VectorBundle.restrictScalars ℝ ℂ F E

/-- **The Euler class of a complex vector bundle** `E → B` of complex rank `r + 1`: the Euler class
`e(E_ℝ) ∈ H²ʳ⁺²(B; ℤ)` of the underlying real bundle with its canonical orientation
`VectorBundleOrientation.complex F E`, reindexed by `Fin (2 * finrank ℂ F) ≃ Fin (2r + 2)`. -/
def complexEulerClass :
    (TopCat.of B).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (2 * r + 2) :=
  (VectorBundleOrientation.reindex (finCongr (by omega))
    (VectorBundleOrientation.complex F E)).eulerClass
    (by rw [finrank_real_eq_two_mul_finrank_complex, hF]; ring)

/-- The Euler class of a complex vector bundle is the Euler class of its canonical orientation,
reindexed along `Fin (2 * finrank ℂ F) ≃ Fin (2r + 2)`. -/
theorem complexEulerClass_def :
    complexEulerClass F E hF =
      (VectorBundleOrientation.reindex (finCongr (by omega))
        (VectorBundleOrientation.complex F E)).eulerClass
        (by rw [finrank_real_eq_two_mul_finrank_complex, hF]; ring) :=
  (rfl)

/-- **Naturality of the Euler class of a complex vector bundle.** The Euler class of the pullback
`f*E` along a continuous map `f : B' → B` is the pull-back along `f` of the Euler class of `E`. -/
theorem complexEulerClass_pullback {B' : Type w} [TopologicalSpace B'] (f : C(B', B)) :
    complexEulerClass F ((⇑f) *ᵖ E) hF =
      TopCat.singularCohomologyMap (TopCat.ofHom f) (2 * r + 2) (complexEulerClass F E hF) := by
  rw [complexEulerClass_def, complexEulerClass_def,
    ← VectorBundleOrientation.pullback_complex, ← VectorBundleOrientation.pullback_reindex]
  exact VectorBundleOrientation.eulerClass_pullback _ _ f

/-- **A nowhere-vanishing section kills the Euler class of a complex vector bundle.** If `E` has a
continuous section `s` with `s b ≠ 0` for every `b`, then `e(E_ℝ) = 0`. -/
theorem complexEulerClass_eq_zero_of_forall_ne_zero {s : ∀ b, E b}
    (hs : Continuous fun b ↦ TotalSpace.mk' F b (s b)) (hs₀ : ∀ b, s b ≠ 0) :
    complexEulerClass F E hF = 0 :=
  VectorBundleOrientation.eulerClass_eq_zero_of_forall_ne_zero _ _ hs hs₀

variable (B) in
/-- **The Euler class of a trivial complex vector bundle vanishes**: the trivial bundle `B × F` of
positive complex rank has a nonzero constant section. -/
@[simp]
theorem complexEulerClass_trivial : complexEulerClass F (Bundle.Trivial B F) hF = 0 := by
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  rw [complexEulerClass_def, VectorBundleOrientation.eulerClass_def,
    TauCeti.eulerClass_trivial_eq_zero]
  rfl

end TauCeti
