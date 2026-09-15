/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

import Mathlib.Tactic.Abel

/-!
# The homogeneous form of a low-degree cochain

An inhomogeneous `n`-cochain `f` of `G` with values in `M` has a homogeneous partner, the
`G`-equivariant function of `n + 1` group elements

```text
homogeneous1 f h₀ h₁ = h₀ • f (h₀⁻¹ h₁),
homogeneous2 f h₀ h₁ h₂ = h₀ • f (h₀⁻¹ h₁, h₁⁻¹ h₂),
```

which this file builds in degrees one and two.  Equivariance
(`TauCeti.ContCohomology.homogeneous2_smul`) is definitional bookkeeping; the point of the
homogeneous form is that the cocycle and coboundary conditions become *symmetric* in the
arguments.  A `2`-cocycle becomes the four-term relation
`TauCeti.ContCohomology.homogeneous2_add_eq_add`, which says that the alternating sum over
dropping one of four points vanishes, and the coboundary of a `1`-cochain becomes the alternating
sum `TauCeti.ContCohomology.homogeneous2_d1` of its own homogeneous form.

The reason to have the symmetric form is `TauCeti.ContCohomology.homogeneous2_sub_comp`: for an
**arbitrary** map `v : G → G`, the values of a homogeneous `2`-cocycle at three points and at
their images under `v` differ by the alternating sum of the explicit homogeneous `1`-cochain
`TauCeti.ContCohomology.homogeneousHomotopy2`. This pointwise prism identity, applied to a
retraction of `G` onto a subgroup, is the comparison used in Shapiro's lemma.

Mathlib's `Rep.diagonalHomEquiv` is the bundled `k`-linear version of the same correspondence, for
`Rep k G` and the diagonal resolution, and `ContinuousCohomology.homogeneousCochains` is the
all-degree homogeneous complex computing the canonical carrier.  Neither applies to the unbundled
`DistribMulAction`-valued continuous cochains of
`TauCeti/RepresentationTheory/Homological/ContCohomology/LowDegree.lean`, which is what the
declarations below are stated for; nothing here builds a competing cohomology theory, only a
change of coordinates on the cochains of that file.

## Main definitions

* `TauCeti.ContCohomology.homogeneous1` and `TauCeti.ContCohomology.homogeneous2`: the homogeneous
  forms of a `1`- and a `2`-cochain.
* `TauCeti.ContCohomology.homogeneousHomotopy2`: the homogeneous `1`-cochain comparing the values
  of a homogeneous `2`-cocycle at points with its values at their images under a self-map of `G`.

## Main statements

* `TauCeti.ContCohomology.homogeneous2_add_eq_add`: the homogeneous four-term form of the
  `2`-cocycle identity.
* `TauCeti.ContCohomology.homogeneous2_d1`: the homogeneous form of a `2`-coboundary is the
  alternating sum of the homogeneous form of its primitive.
* `TauCeti.ContCohomology.homogeneous2_sub_comp`: the values of a homogeneous `2`-cocycle at
  points and at their images under an arbitrary self-map of `G` differ by an alternating sum.
* `TauCeti.ContCohomology.continuous_homogeneous1` and
  `TauCeti.ContCohomology.continuous_homogeneous2`: continuity of the homogeneous forms read along
  continuous families of group elements.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I §2, where
  the homogeneous and inhomogeneous descriptions of the standard complex are compared.
-/

public section

namespace TauCeti.ContCohomology

universe u v

variable {G : Type u} [Group G] {M : Type v}

section MulAction

variable [MulAction G M]

/-- The homogeneous form `h₀ • f (h₀⁻¹ h₁)` of a `1`-cochain `f`. -/
def homogeneous1 (f : G → M) (h₀ h₁ : G) : M := h₀ • f (h₀⁻¹ * h₁)

/-- The homogeneous form `h₀ • f (h₀⁻¹ h₁, h₁⁻¹ h₂)` of a `2`-cochain `f`. -/
def homogeneous2 (f : G × G → M) (h₀ h₁ h₂ : G) : M := h₀ • f (h₀⁻¹ * h₁, h₁⁻¹ * h₂)

/-- The defining formula for the homogeneous form of a `1`-cochain. -/
@[simp]
theorem homogeneous1_apply (f : G → M) (h₀ h₁ : G) :
    homogeneous1 f h₀ h₁ = h₀ • f (h₀⁻¹ * h₁) := (rfl)

/-- The defining formula for the homogeneous form of a `2`-cochain. -/
@[simp]
theorem homogeneous2_apply (f : G × G → M) (h₀ h₁ h₂ : G) :
    homogeneous2 f h₀ h₁ h₂ = h₀ • f (h₀⁻¹ * h₁, h₁⁻¹ * h₂) := (rfl)

/-- At the identity the homogeneous form of a `1`-cochain is the cochain itself. Not a `simp`
lemma: `TauCeti.ContCohomology.homogeneous1_apply` already rewrites the left-hand side. -/
theorem homogeneous1_one_left (f : G → M) (h : G) : homogeneous1 f 1 h = f h := by simp

/-- At the identity the homogeneous form of a `2`-cochain is the cochain itself, read at the
second point and the difference of the two. Not a `simp` lemma:
`TauCeti.ContCohomology.homogeneous2_apply` already rewrites the left-hand side. -/
theorem homogeneous2_one_left (f : G × G → M) (h₁ h₂ : G) :
    homogeneous2 f 1 h₁ h₂ = f (h₁, h₁⁻¹ * h₂) := by simp

/-- The homogeneous form of a `1`-cochain is equivariant. -/
theorem homogeneous1_smul (f : G → M) (g h₀ h₁ : G) :
    homogeneous1 f (g * h₀) (g * h₁) = g • homogeneous1 f h₀ h₁ := by
  simp [mul_smul, mul_inv_rev, mul_assoc]

/-- The homogeneous form of a `2`-cochain is equivariant. -/
theorem homogeneous2_smul (f : G × G → M) (g h₀ h₁ h₂ : G) :
    homogeneous2 f (g * h₀) (g * h₁) (g * h₂) = g • homogeneous2 f h₀ h₁ h₂ := by
  simp [mul_smul, mul_inv_rev, mul_assoc]

end MulAction

section Subtraction

variable [AddGroup M] [DistribMulAction G M]

/-- The homogeneous `1`-cochain in the pointwise prism identity comparing a homogeneous
`2`-cocycle at points with its values at their images under a self-map `v` of `G`; see
`TauCeti.ContCohomology.homogeneous2_sub_comp`. -/
def homogeneousHomotopy2 (f : G × G → M) (v : G → G) (h₀ h₁ : G) : M :=
  homogeneous2 f (v h₀) h₀ h₁ - homogeneous2 f (v h₀) (v h₁) h₁

/-- The defining formula for the comparison cochain. It is not a `simp` lemma: its right-hand side
is rewritten further by `TauCeti.ContCohomology.homogeneous2_apply`. -/
theorem homogeneousHomotopy2_apply (f : G × G → M) (v : G → G) (h₀ h₁ : G) :
    homogeneousHomotopy2 f v h₀ h₁ =
      homogeneous2 f (v h₀) h₀ h₁ - homogeneous2 f (v h₀) (v h₁) h₁ := (rfl)

/-- The comparison cochain is equivariant for any `g` that `v` commutes with. -/
theorem homogeneousHomotopy2_smul (f : G × G → M) (v : G → G) {g : G}
    (hv : ∀ x : G, v (g * x) = g * v x) (h₀ h₁ : G) :
    homogeneousHomotopy2 f v (g * h₀) (g * h₁) = g • homogeneousHomotopy2 f v h₀ h₁ := by
  simp only [homogeneousHomotopy2_apply, hv, homogeneous2_smul, smul_sub]

end Subtraction

section Cocycles

variable [AddCommGroup M] [DistribMulAction G M]

/-- **The homogeneous `2`-cocycle identity.** For a `2`-cocycle the alternating sum of the four
values obtained by dropping one of four group elements vanishes, here written as the equality of
the two positive halves. -/
theorem homogeneous2_add_eq_add {f : G × G → M} (hf : groupCohomology.IsCocycle₂ f)
    (h₀ h₁ h₂ h₃ : G) :
    homogeneous2 f h₁ h₂ h₃ + homogeneous2 f h₀ h₁ h₃ =
      homogeneous2 f h₀ h₂ h₃ + homogeneous2 f h₀ h₁ h₂ := by
  have key := hf (h₀⁻¹ * h₁) (h₁⁻¹ * h₂) (h₂⁻¹ * h₃)
  have h₀₂ : h₀⁻¹ * h₁ * (h₁⁻¹ * h₂) = h₀⁻¹ * h₂ := by group
  have h₁₃ : h₁⁻¹ * h₂ * (h₂⁻¹ * h₃) = h₁⁻¹ * h₃ := by group
  rw [h₀₂, h₁₃] at key
  have hsmul := congrArg (fun x : M => h₀ • x) key
  simp only [smul_add, ← mul_smul, mul_inv_cancel_left] at hsmul
  simpa only [homogeneous2_apply] using hsmul.symm

/-- The homogeneous form of a `2`-coboundary is the alternating sum of the homogeneous form of its
primitive. -/
theorem homogeneous2_d1 (f : G → M) (h₀ h₁ h₂ : G) :
    homogeneous2 (d1 G M f) h₀ h₁ h₂ =
      homogeneous1 f h₁ h₂ - homogeneous1 f h₀ h₂ + homogeneous1 f h₀ h₁ := by
  have h₀₂ : h₀⁻¹ * h₁ * (h₁⁻¹ * h₂) = h₀⁻¹ * h₂ := by group
  simp only [homogeneous2_apply, homogeneous1_apply, d1_apply, smul_sub, smul_add, ← mul_smul,
    mul_inv_cancel_left, h₀₂]

/-- **Pointwise prism identity for a homogeneous `2`-cocycle.** Its values at three points and at
their images under any self-map `v` differ by the displayed alternating sum. No equivariance is
assumed of `v`, so this is a pointwise identity rather than an induced map of resolutions. -/
theorem homogeneous2_sub_comp {f : G × G → M} (hf : groupCohomology.IsCocycle₂ f) (v : G → G)
    (h₀ h₁ h₂ : G) :
    homogeneous2 f h₀ h₁ h₂ - homogeneous2 f (v h₀) (v h₁) (v h₂) =
      homogeneousHomotopy2 f v h₁ h₂ - homogeneousHomotopy2 f v h₀ h₂
        + homogeneousHomotopy2 f v h₀ h₁ := by
  have e1 := homogeneous2_add_eq_add hf (v h₀) h₀ h₁ h₂
  have e2 := homogeneous2_add_eq_add hf (v h₀) (v h₁) h₁ h₂
  have e3 := homogeneous2_add_eq_add hf (v h₀) (v h₁) (v h₂) h₂
  -- Peel the three points `v h₀`, `v h₁`, `v h₂` off one at a time, each step being one instance
  -- of the four-term relation.
  have g1 : homogeneous2 f h₀ h₁ h₂ =
      homogeneous2 f (v h₀) h₁ h₂ + homogeneous2 f (v h₀) h₀ h₁ -
        homogeneous2 f (v h₀) h₀ h₂ := by
    rw [← e1]; abel
  have g2 : homogeneous2 f (v h₀) h₁ h₂ =
      homogeneous2 f (v h₁) h₁ h₂ + homogeneous2 f (v h₀) (v h₁) h₂ -
        homogeneous2 f (v h₀) (v h₁) h₁ := by
    rw [e2]; abel
  have g3 : homogeneous2 f (v h₀) (v h₁) h₂ =
      homogeneous2 f (v h₀) (v h₂) h₂ + homogeneous2 f (v h₀) (v h₁) (v h₂) -
        homogeneous2 f (v h₁) (v h₂) h₂ := by
    rw [← e3]; abel
  simp only [homogeneousHomotopy2_apply]
  rw [g1, g2, g3]
  abel

end Cocycles

section Topology

variable [MulAction G M] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M]
  [ContinuousSMul G M] {X : Type*} [TopologicalSpace X]

/-- The homogeneous form of a continuous `1`-cochain, read along continuous families of group
elements, is continuous. -/
theorem continuous_homogeneous1 {f : G → M} (hf : Continuous f) {a b : X → G}
    (ha : Continuous a) (hb : Continuous b) :
    Continuous fun x => homogeneous1 f (a x) (b x) := by
  simp only [homogeneous1_apply]
  exact continuous_smul.comp (ha.prodMk (hf.comp (ha.inv.mul hb)))

/-- The homogeneous form of a continuous `2`-cochain, read along continuous families of group
elements, is continuous. -/
theorem continuous_homogeneous2 {f : G × G → M} (hf : Continuous f) {a b d : X → G}
    (ha : Continuous a) (hb : Continuous b) (hd : Continuous d) :
    Continuous fun x => homogeneous2 f (a x) (b x) (d x) := by
  simp only [homogeneous2_apply]
  exact continuous_smul.comp (ha.prodMk (hf.comp ((ha.inv.mul hb).prodMk (hb.inv.mul hd))))

end Topology

end TauCeti.ContCohomology
