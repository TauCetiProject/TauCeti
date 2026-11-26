/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.FlatTorus.Inverse
public import TauCeti.Analysis.Normed.Lp.PiLp
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# The inverse of the Cauchy–Riemann operator on the divisor bundle of a flat line

Let `ω₁, ω₂ ∈ ℂ` be linearly independent over `ℝ` and let `N` be the flat Hermitian line over the
torus `ℂ / (ℤ ω₁ + ℤ ω₂)` with holonomy `exp (2πiθ₁)`, `exp (2πiθ₂)` along `ω₁`, `ω₂`, as in
`TauCeti.Analysis.Complex.Wirtinger.FlatTorus.Inverse`. Its power `N ^ k` is the flat line with
holonomy `exp (2πikθ₁)`, `exp (2πikθ₂)`. The **divisor bundle** of degree `m` is

`N ⊕ N² ⊕ ⋯ ⊕ Nᵐ`.

Near a square-zero pseudoholomorphic torus whose normal line `N` is flat, an `m`-fold cover of the
torus inside the total space of `N` is cut out by a monic polynomial `wᵐ + b₁ wᵐ⁻¹ + ⋯ + bₘ` in the
fibre coordinate `w`, whose coefficient `bₖ` is a section of `Nᵏ`. The coefficient vector
`(b₁, …, bₘ)` is therefore a section of the divisor bundle, and the leading operator of the
Seiberg–Witten equations near the `m`-fold cover acts on it through the Cauchy–Riemann operator
`∂bar` of each summand.

The square-integrable sections of the divisor bundle are the `L²` direct sum of `m` copies of
`L²([0, 1]²)`, the sections in lattice coordinates, the copy with index `j : Fin m` holding the
sections of `N ^ (j + 1)`. If every power `N ^ (j + 1)`, `j < m`, has nontrivial holonomy, the
block-diagonal operator `TauCeti.divisorBundleCRInverse` with blocks the inverses
`TauCeti.flatLineCRInverse` of `∂bar` on the summands is the inverse of `∂bar` on the divisor
bundle: `Q f = y` exactly when each component of `y` is a weak solution of `∂bar y = f` on its
summand (`TauCeti.divisorBundleCRInverse_apply_eq_iff`), so weak solutions exist and are unique,
and `Q` inverts `∂bar` on `C¹` sections
(`TauCeti.divisorBundleCRInverse_ae_eq_of_ae_eq_conjWirtingerDeriv`). Its norm is at most the
largest of the norm bounds `C_k^(-1/2)` of the summands, with
`C_k = π² / 2 · (‖k θ₁‖ℤ² / |ω₁|² + ‖k θ₂‖ℤ² / |ω₂|²)` and `‖x‖ℤ` the distance to the nearest
integer (`TauCeti.norm_divisorBundleCRInverse_le`). The inverse gains one derivative: with the
Beurling transform `TauCeti.divisorBundleBeurling` of the divisor bundle, an isometry on its
square-integrable sections, the section `Q f` has the weak derivative
`v • divisorBundleBeurling f + conj v • f` along every direction `v`, of norm at most
`2 ‖v‖ ‖f‖` (`TauCeti.setIntegral_divisorBundleCRInverse_mul_conj_fderiv`,
`TauCeti.norm_smul_divisorBundleBeurling_add_smul_le`).

If the holonomy of `N` has infinite order, that is if `θ₁` or `θ₂` is irrational, every power of
`N` pulled back to every finite cover of the torus is nontrivial
(`TauCeti.notMem_range_intCast_or_notMem_range_intCast_of_irrational`). A finite cover is the
torus of a sublattice with basis `a ω₁ + b ω₂, c ω₁ + d ω₂`, `a d - b c ≠ 0`, on which the pulled
back line has twists `a θ₁ + b θ₂` and `c θ₁ + d θ₂`. So `∂bar` is invertible on the divisor bundle
of every degree over every finite cover
(`TauCeti.divisorBundleCRInverse_apply_eq_iff_of_irrational`).

## Main definitions

* `TauCeti.divisorBundleCRInverse`: the inverse of `∂bar` on the square-integrable sections of the
  divisor bundle `N ⊕ N² ⊕ ⋯ ⊕ Nᵐ`.
* `TauCeti.divisorBundleBeurling`: the Beurling transform `∂bar u ↦ ∂u` of the divisor bundle.

## Main results

* `TauCeti.divisorBundleCRInverse_apply_eq_iff`: the inverse sends `f` to the unique weak solution
  of `∂bar y = f`.
* `TauCeti.divisorBundleCRInverse_ae_eq_of_ae_eq_conjWirtingerDeriv`: it inverts `∂bar` on `C¹`
  sections.
* `TauCeti.norm_divisorBundleCRInverse_le`: its norm is at most the largest norm bound of the
  summands.
* `TauCeti.divisorBundleBeurling_ae_eq_of_ae_eq_conjWirtingerDeriv`: the Beurling transform
  sends `∂bar u` to `∂u` on `C²` sections.
* `TauCeti.norm_divisorBundleBeurling_apply`: the Beurling transform is an isometry.
* `TauCeti.setIntegral_divisorBundleCRInverse_mul_conj_fderiv`,
  `TauCeti.norm_smul_divisorBundleBeurling_add_smul_le`: the inverse maps `L²` into `H¹`.
* `TauCeti.divisorBundleCRInverse_apply_eq_iff_of_irrational`: for a flat line with infinite
  holonomy, `∂bar` is invertible on the divisor bundle of every degree over every finite cover.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818–893.
-/

public section

open Complex ComplexConjugate MeasureTheory Set
open scoped Real

namespace TauCeti

variable {ω₁ ω₂ : ℂ} {θ₁ θ₂ : ℝ} {m : ℕ}

/-! ### The inverse of `∂bar` -/

section Inverse

/-- **The inverse of `∂bar` on the divisor bundle** `N ⊕ N² ⊕ ⋯ ⊕ Nᵐ` of the flat line `N` with
holonomy `exp (2πiθ₁)`, `exp (2πiθ₂)` along `ω₁`, `ω₂`. It acts on the `L²` direct sum of `m`
copies of `L²([0, 1]²)`, the copy with index `j` holding the sections of `N ^ (j + 1)` in lattice
coordinates, as the inverse `TauCeti.flatLineCRInverse` of `∂bar` on each summand. It is the
inverse of `∂bar` when every summand has nontrivial holonomy
(`TauCeti.divisorBundleCRInverse_apply_eq_iff`). -/
noncomputable def divisorBundleCRInverse (ω₁ ω₂ : ℂ) (θ₁ θ₂ : ℝ) (m : ℕ) :
    PiLp 2 (fun _ : Fin m ↦
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))) →L[ℂ]
      PiLp 2 (fun _ : Fin m ↦
        Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))) :=
  PiLp.piMap 2 fun j ↦ flatLineCRInverse ω₁ ω₂ (((j : ℕ) + 1 : ℝ) * θ₁) (((j : ℕ) + 1 : ℝ) * θ₂)

/-- The component of index `j` of `divisorBundleCRInverse ω₁ ω₂ θ₁ θ₂ m f` is the inverse of
`∂bar` on `N ^ (j + 1)` applied to the component of index `j` of `f`. -/
@[simp]
theorem divisorBundleCRInverse_apply
    (f : PiLp 2 (fun _ : Fin m ↦
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))))
    (j : Fin m) :
    divisorBundleCRInverse ω₁ ω₂ θ₁ θ₂ m f j =
      flatLineCRInverse ω₁ ω₂ (((j : ℕ) + 1 : ℝ) * θ₁) (((j : ℕ) + 1 : ℝ) * θ₂) (f j) := by
  rw [divisorBundleCRInverse, PiLp.piMap_apply]

variable (hω : (conj ω₁ * ω₂).im ≠ 0)
  (hθ : ∀ j : Fin m, ((j : ℕ) + 1 : ℝ) * θ₁ ∉ range ((↑) : ℤ → ℝ) ∨
    ((j : ℕ) + 1 : ℝ) * θ₂ ∉ range ((↑) : ℤ → ℝ))
include hω hθ

/-- **The inverse of `∂bar` on the divisor bundle.** Let `ω₁, ω₂` be linearly independent over
`ℝ`, and let every power `N ^ (j + 1)`, `j < m`, of the flat line `N` have nontrivial holonomy.
Then `divisorBundleCRInverse ω₁ ω₂ θ₁ θ₂ m f = y` exactly when every component `y j` is a weak
solution of `∂bar (y j) = f j` on `N ^ (j + 1)`: `∫ y j · conj (∂φ) = -∫ f j · conj φ` for every
`C²` section `φ` of `N ^ (j + 1)`. In particular weak solutions exist and are unique. -/
theorem divisorBundleCRInverse_apply_eq_iff
    {f y : PiLp 2 (fun _ : Fin m ↦
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))} :
    divisorBundleCRInverse ω₁ ω₂ θ₁ θ₂ m f = y ↔ ∀ j : Fin m,
      ∀ φ ∈ flatLineTestSections ω₁ ω₂ (((j : ℕ) + 1 : ℝ) * θ₁) (((j : ℕ) + 1 : ℝ) * θ₂),
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
            y j p * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) =
          -∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f j p * conj (φ (p.1 * ω₁ + p.2 * ω₂)) := by
  refine ⟨fun h j ↦ ?_, fun h ↦ PiLp.ext fun j ↦ ?_⟩
  · exact (flatLineCRInverse_apply_eq_iff hω (hθ j)).1 (by rw [← h, divisorBundleCRInverse_apply])
  · rw [divisorBundleCRInverse_apply]
    exact (flatLineCRInverse_apply_eq_iff hω (hθ j)).2 (h j)

/-- **The inverse of `∂bar` inverts `∂bar` on `C¹` sections of the divisor bundle.** If every
power `N ^ (j + 1)`, `j < m`, has nontrivial holonomy, `u j` is a `C¹` section of `N ^ (j + 1)`
for every `j`, and `f j` represents `∂bar (u j)` in lattice coordinates, then the component of
index `j` of `divisorBundleCRInverse ω₁ ω₂ θ₁ θ₂ m f` represents `u j`. -/
theorem divisorBundleCRInverse_ae_eq_of_ae_eq_conjWirtingerDeriv {u : Fin m → ℂ → ℂ}
    (hu : ∀ j, ContDiff ℝ 1 (u j))
    (hu₁ : ∀ j z, u j (z + ω₁) = exp (2 * π * ↑(((j : ℕ) + 1 : ℝ) * θ₁) * I) * u j z)
    (hu₂ : ∀ j z, u j (z + ω₂) = exp (2 * π * ↑(((j : ℕ) + 1 : ℝ) * θ₂) * I) * u j z)
    {f : PiLp 2 (fun _ : Fin m ↦
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))}
    (hf : ∀ j, f j =ᵐ[(volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)]
      fun p ↦ conjWirtingerDeriv (u j) (p.1 * ω₁ + p.2 * ω₂) 1) (j : Fin m) :
    divisorBundleCRInverse ω₁ ω₂ θ₁ θ₂ m f j =ᵐ[(volume : Measure (ℝ × ℝ)).restrict
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)] fun p ↦ u j (p.1 * ω₁ + p.2 * ω₂) := by
  rw [divisorBundleCRInverse_apply]
  exact flatLineCRInverse_ae_eq_of_ae_eq_conjWirtingerDeriv hω (hθ j) (hu j) (hu₁ j) (hu₂ j) (hf j)

/-- **The norm of the inverse of `∂bar` on the divisor bundle.** If every power `N ^ (j + 1)`,
`j < m`, has nontrivial holonomy, the inverse of `∂bar` on the divisor bundle has norm at most the
largest of the bounds `C_(j+1)^(-1/2)` of its summands, where
`C_k = π² / 2 · (‖k θ₁‖ℤ² / |ω₁|² + ‖k θ₂‖ℤ² / |ω₂|²)` and `‖x‖ℤ = |x - round x|`. -/
theorem norm_divisorBundleCRInverse_le :
    ‖divisorBundleCRInverse ω₁ ω₂ θ₁ θ₂ m‖ ≤ ⨆ j : Fin m,
      (√(π ^ 2 / 2 *
        (|((j : ℕ) + 1 : ℝ) * θ₁ - round (((j : ℕ) + 1 : ℝ) * θ₁)| ^ 2 / ‖ω₁‖ ^ 2 +
          |((j : ℕ) + 1 : ℝ) * θ₂ - round (((j : ℕ) + 1 : ℝ) * θ₂)| ^ 2 / ‖ω₂‖ ^ 2)))⁻¹ :=
  PiLp.norm_piMap_le (Real.iSup_nonneg fun _ ↦ by positivity) fun j ↦
    le_ciSup_of_le (finite_range _).bddAbove j (norm_flatLineCRInverse_le hω (hθ j))

end Inverse

/-! ### The Beurling transform and the gain of one derivative -/

section Regularity

/-- **The Beurling transform of the divisor bundle** `N ⊕ N² ⊕ ⋯ ⊕ Nᵐ`: the operator
`∂bar u ↦ ∂u` on its square-integrable sections, acting on each summand `N ^ (j + 1)` as its
Beurling transform `TauCeti.flatLineBeurling`. It is a contraction
(`TauCeti.norm_divisorBundleBeurling_le`), an isometry when every summand has nontrivial holonomy
(`TauCeti.norm_divisorBundleBeurling_apply`), and it computes the weak `∂`-derivative of
`TauCeti.divisorBundleCRInverse`. -/
noncomputable def divisorBundleBeurling (ω₁ ω₂ : ℂ) (θ₁ θ₂ : ℝ) (m : ℕ) :
    PiLp 2 (fun _ : Fin m ↦
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))) →L[ℂ]
      PiLp 2 (fun _ : Fin m ↦
        Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))) :=
  PiLp.piMap 2 fun j ↦ flatLineBeurling ω₁ ω₂ (((j : ℕ) + 1 : ℝ) * θ₁) (((j : ℕ) + 1 : ℝ) * θ₂)

/-- The component of index `j` of `divisorBundleBeurling ω₁ ω₂ θ₁ θ₂ m f` is the Beurling
transform of `N ^ (j + 1)` applied to the component of index `j` of `f`. -/
@[simp]
theorem divisorBundleBeurling_apply
    (f : PiLp 2 (fun _ : Fin m ↦
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))))
    (j : Fin m) :
    divisorBundleBeurling ω₁ ω₂ θ₁ θ₂ m f j =
      flatLineBeurling ω₁ ω₂ (((j : ℕ) + 1 : ℝ) * θ₁) (((j : ℕ) + 1 : ℝ) * θ₂) (f j) := by
  rw [divisorBundleBeurling, PiLp.piMap_apply]

variable (hω : (conj ω₁ * ω₂).im ≠ 0)
include hω

/-- **The Beurling transform of the divisor bundle sends `∂bar u` to `∂u`.** If `ω₁, ω₂` are
linearly independent over `ℝ`, `u j` is a `C²` section of `N ^ (j + 1)` for every `j`, and `f j`
represents `∂bar (u j)` in lattice coordinates, then the component of index `j` of
`divisorBundleBeurling ω₁ ω₂ θ₁ θ₂ m f` represents `∂ (u j)`. -/
theorem divisorBundleBeurling_ae_eq_of_ae_eq_conjWirtingerDeriv {u : Fin m → ℂ → ℂ}
    (hu : ∀ j, ContDiff ℝ 2 (u j))
    (hu₁ : ∀ j z, u j (z + ω₁) = exp (2 * π * ↑(((j : ℕ) + 1 : ℝ) * θ₁) * I) * u j z)
    (hu₂ : ∀ j z, u j (z + ω₂) = exp (2 * π * ↑(((j : ℕ) + 1 : ℝ) * θ₂) * I) * u j z)
    {f : PiLp 2 (fun _ : Fin m ↦
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))}
    (hf : ∀ j, f j =ᵐ[(volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)]
      fun p ↦ conjWirtingerDeriv (u j) (p.1 * ω₁ + p.2 * ω₂) 1) (j : Fin m) :
    divisorBundleBeurling ω₁ ω₂ θ₁ θ₂ m f j =ᵐ[(volume : Measure (ℝ × ℝ)).restrict
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)] fun p ↦ wirtingerDeriv (u j) (p.1 * ω₁ + p.2 * ω₂) 1 := by
  rw [divisorBundleBeurling_apply]
  exact flatLineBeurling_ae_eq_of_ae_eq_conjWirtingerDeriv hω (hu j) (hu₁ j) (hu₂ j) (hf j)

/-- The Beurling transform of the divisor bundle is a contraction. -/
theorem norm_divisorBundleBeurling_le : ‖divisorBundleBeurling ω₁ ω₂ θ₁ θ₂ m‖ ≤ 1 :=
  PiLp.norm_piMap_le zero_le_one fun _ ↦ norm_flatLineBeurling_le hω

/-- **The weak derivatives of the inverse of `∂bar` on the divisor bundle are bounded.** For every
square-integrable section `f` of the divisor bundle and every direction `v ∈ ℂ`,
`‖v • divisorBundleBeurling f + conj v • f‖ ≤ 2 ‖v‖ ‖f‖`. -/
theorem norm_smul_divisorBundleBeurling_add_smul_le
    (f : PiLp 2 (fun _ : Fin m ↦
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))))
    (v : ℂ) :
    ‖v • divisorBundleBeurling ω₁ ω₂ θ₁ θ₂ m f + conj v • f‖ ≤ 2 * ‖v‖ * ‖f‖ :=
  ContinuousLinearMap.norm_smul_apply_add_conj_smul_le (norm_divisorBundleBeurling_le hω) v f

variable (hθ : ∀ j : Fin m, ((j : ℕ) + 1 : ℝ) * θ₁ ∉ range ((↑) : ℤ → ℝ) ∨
    ((j : ℕ) + 1 : ℝ) * θ₂ ∉ range ((↑) : ℤ → ℝ))
include hθ

/-- **The Beurling transform of the divisor bundle is an isometry** when every power
`N ^ (j + 1)`, `j < m`, has nontrivial holonomy. -/
theorem norm_divisorBundleBeurling_apply
    (f : PiLp 2 (fun _ : Fin m ↦
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))) :
    ‖divisorBundleBeurling ω₁ ω₂ θ₁ θ₂ m f‖ = ‖f‖ := by
  simp only [PiLp.norm_eq_of_L2, divisorBundleBeurling_apply,
    norm_flatLineBeurling_apply hω (hθ _)]

/-- **The inverse of `∂bar` on the divisor bundle gains one derivative.** If every power
`N ^ (j + 1)`, `j < m`, has nontrivial holonomy, then for every square-integrable section `f` of
the divisor bundle and every direction `v ∈ ℂ`, each component of
`Q f = divisorBundleCRInverse ω₁ ω₂ θ₁ θ₂ m f` has the corresponding component of
`v • divisorBundleBeurling f + conj v • f` as its weak derivative along `v`: for every `C²`
section `φ` of `N ^ (j + 1)`, `∫ (Q f) j · conj (Dφ v) = -∫ (v • divisorBundleBeurling f +
conj v • f) j · conj φ`. Its norm is at most `2 ‖v‖ ‖f‖`
(`TauCeti.norm_smul_divisorBundleBeurling_add_smul_le`), so `Q f` lies in `H¹`. -/
theorem setIntegral_divisorBundleCRInverse_mul_conj_fderiv
    (f : PiLp 2 (fun _ : Fin m ↦
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))))
    (j : Fin m) {φ : ℂ → ℂ}
    (hφ : φ ∈ flatLineTestSections ω₁ ω₂ (((j : ℕ) + 1 : ℝ) * θ₁) (((j : ℕ) + 1 : ℝ) * θ₂))
    (v : ℂ) :
    ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        divisorBundleCRInverse ω₁ ω₂ θ₁ θ₂ m f j p *
          conj (fderiv ℝ φ (p.1 * ω₁ + p.2 * ω₂) v) =
      -∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        (v • divisorBundleBeurling ω₁ ω₂ θ₁ θ₂ m f + conj v • f) j p *
          conj (φ (p.1 * ω₁ + p.2 * ω₂)) := by
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, divisorBundleBeurling_apply,
    divisorBundleCRInverse_apply]
  exact setIntegral_flatLineCRInverse_mul_conj_fderiv hω (hθ j) (f j) hφ v

end Regularity

/-! ### Finite covers of a flat line with infinite holonomy -/

section Irrational

/-- **`∂bar` is invertible on the divisor bundle over every finite cover.** Let `ω₁, ω₂` be
linearly independent over `ℝ`, let `θ₁` or `θ₂` be irrational, and let `a d - b c ≠ 0`. On the
torus of the sublattice with basis `ω₁' = a ω₁ + b ω₂`, `ω₂' = c ω₁ + d ω₂`, where the pull-back of
the flat line `N` has twists `θ₁' = a θ₁ + b θ₂` and `θ₂' = c θ₁ + d θ₂`, the inverse of `∂bar` on
the divisor bundle of degree `m` sends `f` to `y` exactly when every component `y j` is a weak
solution of `∂bar (y j) = f j` on `N ^ (j + 1)`. -/
theorem divisorBundleCRInverse_apply_eq_iff_of_irrational (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : Irrational θ₁ ∨ Irrational θ₂) {a b c d : ℤ} (hdet : a * d - b * c ≠ 0)
    {f y : PiLp 2 (fun _ : Fin m ↦
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))} :
    divisorBundleCRInverse (a * ω₁ + b * ω₂) (c * ω₁ + d * ω₂) (a * θ₁ + b * θ₂)
        (c * θ₁ + d * θ₂) m f = y ↔ ∀ j : Fin m,
      ∀ φ ∈ flatLineTestSections (a * ω₁ + b * ω₂) (c * ω₁ + d * ω₂)
          (((j : ℕ) + 1 : ℝ) * (a * θ₁ + b * θ₂)) (((j : ℕ) + 1 : ℝ) * (c * θ₁ + d * θ₂)),
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
            y j p * conj (wirtingerDeriv φ (p.1 * (a * ω₁ + b * ω₂) + p.2 * (c * ω₁ + d * ω₂)) 1) =
          -∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
            f j p * conj (φ (p.1 * (a * ω₁ + b * ω₂) + p.2 * (c * ω₁ + d * ω₂))) :=
  divisorBundleCRInverse_apply_eq_iff (im_conj_intCast_mul_add_mul_intCast_mul_add_ne_zero hω hdet)
    fun j ↦ by
      -- Every power `N ^ (j + 1)` of the pulled-back line is nontrivial.
      have h := notMem_range_intCast_or_notMem_range_intCast_of_irrational hθ
        (j := ((j : ℕ) : ℤ) + 1) (by omega) hdet
      push_cast at h
      exact h

end Irrational

end TauCeti
