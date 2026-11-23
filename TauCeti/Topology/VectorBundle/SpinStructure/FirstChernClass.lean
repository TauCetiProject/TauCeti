/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Associated.Pullback
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass
public import TauCeti.Topology.VectorBundle.SpinStructure.Spinor
import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv

/-!
# The first Chern class of a `Spinᶜ` structure

The **first Chern class** `c₁(𝔰) ∈ H²(X; ℤ)` of a `Spinᶜ` structure `𝔰` on a real vector bundle
`E → X` (`TauCeti.SpinCStructure.firstChernClass`) is the first Chern class of its determinant
line `L = P ×_{z²} ℂ` (`TauCeti.SpinCStructure.determinantLine`), the Euler class of the underlying
oriented real plane bundle (`TauCeti.lineFirstChernClass`).

It is natural under pullback (`TauCeti.SpinCStructure.firstChernClass_pullback`): the determinant
line of the pulled-back structure `f^* 𝔰` is, fibre by fibre, the determinant line of `𝔰` at
`f y` (`TauCeti.SpinCStructure.pullbackDeterminantLineEquiv`), through the comparison
`[p, v] ↦ [p, v]` of associating and pulling back (`TauCeti.AssociatedBundle.pullbackEquiv`), so
`c₁(f^* 𝔰) = f^* c₁(𝔰)`.

The determinant model is `ℂ`, a type in the lowest universe, and the first Chern class of a line
bundle is defined for a base in the universe of the model fibre, so the base `X` is a type in the
lowest universe.

## Main definitions

* `TauCeti.SpinCStructure.firstChernClass`: the first Chern class `c₁(𝔰)` of a `Spinᶜ` structure.
* `TauCeti.SpinCStructure.pullbackDeterminantLineEquiv`: the identification of the determinant
  line of `f^* 𝔰` at `y` with that of `𝔰` at `f y`.

## Main results

* `TauCeti.SpinCStructure.firstChernClass_pullback`: `c₁(f^* 𝔰) = f^* c₁(𝔰)`.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
* R. C. Kirby, *The topology of 4-manifolds*, Lecture Notes in Mathematics 1374, Springer, 1989,
  Chapter IV.
-/

public section

noncomputable section

open Bundle CliffordAlgebra Module

namespace TauCeti

namespace SpinCStructure

variable {n : ℕ} [NeZero n]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQn" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)

variable (n) in
omit [NeZero n] in
/-- The determinant model has complex dimension one. -/
theorem finrank_determinantModel : finrank ℂ (DeterminantModel n) = 1 :=
  (DeterminantModel.toComplex (n := n)).finrank_eq.trans (finrank_self ℂ)

variable {X : Type} [TopologicalSpace X] {F : Type*} {E : X → Type*}
  [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]

/-- **The first Chern class of a `Spinᶜ` structure**: `c₁(𝔰) ∈ H²(X; ℤ)`, the first Chern class of
its determinant line. -/
def firstChernClass (s : SpinCStructure F E n) :
    (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) 2 :=
  lineFirstChernClass (DeterminantModel n) s.determinantLine (finrank_determinantModel n)

/-- `c₁(𝔰)` is the first Chern class of the determinant line of `𝔰`. -/
theorem firstChernClass_def (s : SpinCStructure F E n) :
    s.firstChernClass =
      lineFirstChernClass (DeterminantModel n) s.determinantLine (finrank_determinantModel n) :=
  (rfl)

variable {Y : Type} [TopologicalSpace Y] (s : SpinCStructure F E n) (f : C(Y, X))

/-- The determinant line of the pulled-back `Spinᶜ` structure `f^* 𝔰` at `y` is the determinant
line of `𝔰` at `f y`: the class `[p, v]` goes to `[p, v]`
(`TauCeti.SpinCStructure.pullbackDeterminantLineEquiv_apply`). -/
def pullbackDeterminantLineEquiv (y : Y) :
    determinantLine (s.pullback f) y ≃L[ℂ] s.determinantLine (f y) :=
  let p : s.P (f y) :=
    (FiberBundle.homeomorphAt (spinCGroup (realCliffordForm n 0) hQn) s.P (f y)).symm 1
  (AssociatedBundle.mkContinuousLinearEquiv ℂ (spinCGroup (realCliffordForm n 0) hQn)
      (P := (s.pullback f).P) (F := DeterminantModel n) p).symm.trans
    (AssociatedBundle.mkContinuousLinearEquiv ℂ (spinCGroup (realCliffordForm n 0) hQn)
      (P := s.P) (F := DeterminantModel n) p)

/-- The identification of determinant lines is the comparison
`TauCeti.AssociatedBundle.pullbackEquiv` of associating and pulling back, which sends `[p, v]` to
`[p, v]`. -/
theorem pullbackDeterminantLineEquiv_apply (y : Y) (v : determinantLine (s.pullback f) y) :
    s.pullbackDeterminantLineEquiv f y v = AssociatedBundle.pullbackEquiv f y v := by
  set p : s.P (f y) :=
    (FiberBundle.homeomorphAt (spinCGroup (realCliffordForm n 0) hQn) s.P (f y)).symm 1
  set e := AssociatedBundle.mkContinuousLinearEquiv ℂ (spinCGroup (realCliffordForm n 0) hQn)
    (P := (s.pullback f).P) (F := DeterminantModel n) p
  obtain ⟨w, rfl⟩ := e.surjective v
  have h : e.symm (e w) = w := e.symm_apply_apply w
  have h' : AssociatedBundle.pullbackEquiv f y (e w) =
      AssociatedBundle.mk (spinCGroup (realCliffordForm n 0) hQn) (P := s.P) p w :=
    (congrArg (AssociatedBundle.pullbackEquiv f y) (AssociatedBundle.mkContinuousLinearEquiv_apply
      (G := spinCGroup (realCliffordForm n 0) hQn) (P := (s.pullback f).P) (𝕜 := ℂ) p w)).trans
      (AssociatedBundle.pullbackEquiv_mk f y p w)
  rw [h', pullbackDeterminantLineEquiv, ContinuousLinearEquiv.trans_apply]
  exact (congrArg _ h).trans (AssociatedBundle.mkContinuousLinearEquiv_apply p w)

/-- **Naturality of the first Chern class**: `c₁(f^* 𝔰) = f^* c₁(𝔰)` for a continuous map
`f : Y → X`. -/
theorem firstChernClass_pullback :
    firstChernClass (s.pullback f) =
      TopCat.singularCohomologyMap (TopCat.ofHom f) 2 s.firstChernClass := by
  rw [firstChernClass_def, firstChernClass_def, lineFirstChernClass_def,
    lineFirstChernClass_def]
  refine complexEulerClass_eq_singularCohomologyMap_of_fiberwise (F := DeterminantModel n)
    (E := s.determinantLine) (F' := DeterminantModel n) (E' := determinantLine (s.pullback f))
    (g := f) (finrank_determinantModel n) (finrank_determinantModel n)
    (φ := fun y ↦ s.pullbackDeterminantLineEquiv f y) ?_
  have h := (Pullback.continuous_lift (DeterminantModel n) s.determinantLine f).comp
    (AssociatedBundle.pullbackHomeomorph (G := spinCGroup (realCliffordForm n 0) hQn) (P := s.P)
      (F := DeterminantModel n) f).continuous
  refine h.congr fun v ↦ ?_
  rw [Function.comp_apply, AssociatedBundle.pullbackHomeomorph_apply,
    pullbackDeterminantLineEquiv_apply]
  rfl

end SpinCStructure

end TauCeti
