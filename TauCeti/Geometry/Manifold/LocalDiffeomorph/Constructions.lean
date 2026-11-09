/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Constructions of partial diffeomorphisms

Basic ways of producing a `PartialDiffeomorph` include lowering the regularity of a given one and
reading a continuous linear equivalence as one at any regularity. Mathlib's
`ContinuousLinearEquiv.toDiffeomorph` gives the latter at regularity `∞` only, so it does not cover
the analytic regularity `ω`. A transition between charts taking specified points to the same
coordinate gives a local change of parameters intertwining those charts.

## Main definitions

* `PartialDiffeomorph.ofLE`: a `C^n` partial diffeomorphism as a `C^m` one, for `m ≤ n`.
* `ContinuousLinearEquiv.toPartialDiffeomorph`: a continuous linear equivalence as a `C^n` partial
  diffeomorphism defined everywhere, for any `n`.

## Main results

* `PartialDiffeomorph.exists_transition`: charts with a common coordinate induce a local change
  of parameters carrying the specified points to one another.
-/

public section

noncomputable section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {m n : WithTop ℕ∞}

namespace PartialDiffeomorph

/-- A `C^n` partial diffeomorphism as a `C^m` one, for `m ≤ n`. -/
def ofLE (Φ : PartialDiffeomorph I J M N n) (hmn : m ≤ n) : PartialDiffeomorph I J M N m where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  contMDiffOn_toFun := Φ.contMDiffOn.of_le hmn
  contMDiffOn_invFun := Φ.symm.contMDiffOn.of_le hmn

/-- Lowering the regularity keeps the underlying partial equivalence. -/
@[simp]
theorem ofLE_toPartialEquiv (Φ : PartialDiffeomorph I J M N n) (hmn : m ≤ n) :
    (Φ.ofLE hmn).toPartialEquiv = Φ.toPartialEquiv :=
  (rfl)

open Set

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

/-- Two charts taking specified source points to the same coordinate induce a local change of
parameters. The transition sends `x` to `y`, stays in both chart domains, and intertwines
the coordinate maps. -/
theorem exists_transition (c : PartialDiffeomorph I K M P n)
    (d : PartialDiffeomorph J K N P n) {x : M} {y : N}
    (hx : x ∈ c.source) (hy : y ∈ d.source) (hxy : c x = d y) :
    ∃ e : PartialDiffeomorph I J M N n,
      x ∈ e.source ∧ e x = y ∧ e.source ⊆ c.source ∧
        MapsTo e e.source d.source ∧ ∀ z ∈ e.source, d (e z) = c z := by
  have hsource : (c.trans d.symm).source = c.source ∩ c ⁻¹' d.target := by
    simp [trans_toPartialEquiv, symm_toPartialEquiv]
  have hcoe (z : M) : (c.trans d.symm) z = d.symm (c z) := by
    simp [trans_toPartialEquiv, symm_toPartialEquiv]
  refine ⟨c.trans d.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsource]
    refine ⟨hx, ?_⟩
    rw [mem_preimage, hxy]
    exact d.map_source hy
  · rw [hcoe, hxy]
    exact d.left_inv hy
  · intro z hz
    exact (hsource ▸ hz).1
  · intro z hz
    rw [hcoe]
    exact d.map_target (hsource ▸ hz).2
  · intro z hz
    rw [hcoe]
    exact d.right_inv (hsource ▸ hz).2


end PartialDiffeomorph

namespace ContinuousLinearEquiv

/-- A continuous linear equivalence as a `C^n` partial diffeomorphism defined everywhere, for any
regularity `n`, including the analytic regularity `ω` not reached by
`ContinuousLinearEquiv.toDiffeomorph`. -/
def toPartialDiffeomorph (A : E ≃L[𝕜] F) : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) E F n where
  toPartialEquiv := A.toEquiv.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := A.contDiff.contMDiff.contMDiffOn
  contMDiffOn_invFun := A.symm.contDiff.contMDiff.contMDiffOn

/-- The partial equivalence underlying `ContinuousLinearEquiv.toPartialDiffeomorph` is the
underlying equivalence, on the whole space. -/
@[simp]
theorem toPartialDiffeomorph_toPartialEquiv (A : E ≃L[𝕜] F) :
    (A.toPartialDiffeomorph (n := n)).toPartialEquiv = A.toEquiv.toPartialEquiv :=
  (rfl)

end ContinuousLinearEquiv
