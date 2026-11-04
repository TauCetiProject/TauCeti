/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# The Lie derivative of endomorphism fields on normed spaces

The Lie derivative of an endomorphism field `A : E → E →L[𝕜] E` along a vector field `V : E → E`
on a normed space `E` is

`L_V A (x) = DA(x)(V x) + A(x) ∘ DV(x) - DV(x) ∘ A(x)`.

As with `TauCeti.lieDerivForm`, the definition needs no flow and is total, with junk values where
`A` or `V` is not differentiable, and `TauCeti.lieDerivEndomorphismWithin` localizes all
derivatives to a set `s`.

Four properties organize the calculus of `L_V A`:

* **Bracket formula** (`lieDerivEndomorphism_apply_vectorField`): on a differentiable vector field
  `W`, `(L_V A)(W) = [V, A W] - A [V, W]`, where `[V, W] = DW · V - DV · W` is Mathlib's
  `VectorField.lieBracket`.
* **Derivation rule on composition** (`lieDerivEndomorphism_comp`):
  `L_V (A ∘ B) = (L_V A) ∘ B + A ∘ (L_V B)`. In particular, if `A² = -1` near `x`, then `L_V A`
  anticommutes with `A(x)` (`lieDerivEndomorphism_comp_add_comp_eq_zero`).
* **Commutator identity and source-bracket sign comparison** (`lieDerivEndomorphism_lieBracket`
  and `lieDerivEndomorphism_fderiv_sub_fderiv`): for `C²` fields `U`, `V`, `A`, Mathlib's Lie
  bracket satisfies `L_{[U, V]} A = L_U (L_V A) - L_V (L_U A)`, whereas the opposite bracket
  `[U, V]_RS = DU · V - DV · U = -[U, V]` used by Robbin–Salamon satisfies
  `L_{[U, V]_RS} A = L_V (L_U A) - L_U (L_V A)`.
* **Nijenhuis–Lie-derivative identity** (`lieDerivEndomorphism_apply_sub_apply`): when
  `A(x)² = -1`, the derivative `DX(x)` cancels from `(L_{A X} A)(w) - A(L_X A)(w)`, leaving the
  pointwise Nijenhuis expression of `A` evaluated on `(X x, w)`.

## Main declarations

* `TauCeti.lieDerivEndomorphismWithin`, `TauCeti.lieDerivEndomorphism`: the Lie derivative of an
  endomorphism field within a set and on the whole space.
* `TauCeti.lieDerivEndomorphism_apply_vectorField`: `(L_V A)(W) = [V, A W] - A [V, W]`.
* `TauCeti.lieDerivEndomorphism_comp`: `L_V (A ∘ B) = (L_V A) ∘ B + A ∘ (L_V B)`.
* `TauCeti.lieDerivEndomorphism_lieBracket` and
  `TauCeti.lieDerivEndomorphism_fderiv_sub_fderiv`: the native and source-bracket commutator
  identities.
* `TauCeti.lieDerivEndomorphism_apply_sub_apply`: `(L_{A X} A)(w) - A(L_X A)(w)` equals the
  Nijenhuis expression of `A` when `A(x)² = -1`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, Proposition 3.2 (Lie derivative of tensor fields and bracket commutator).
* J. W. Robbin and D. A. Salamon, *Corrigendum to A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 9 (2007), 901–905 (endomorphism Lie derivative and bracket convention).
-/

public section

noncomputable section

open Set Filter VectorField
open scoped Topology ContDiff

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U V V₁ W : E → E} {A A₁ B : E → E →L[𝕜] E} {s : Set E} {x : E}

/-- The Lie derivative within `s` at `x` of an endomorphism field `A` along a vector field `V`:
`DA|_s(x)(V x) + A(x) ∘ DV|_s(x) - DV|_s(x) ∘ A(x)`. -/
def lieDerivEndomorphismWithin (V : E → E) (A : E → E →L[𝕜] E) (s : Set E) (x : E) :
    E →L[𝕜] E :=
  fderivWithin 𝕜 A s x (V x) +
    (A x).comp (fderivWithin 𝕜 V s x) - (fderivWithin 𝕜 V s x).comp (A x)

/-- The Lie derivative at `x` of an endomorphism field `A` along a vector field `V`:
`DA(x)(V x) + A(x) ∘ DV(x) - DV(x) ∘ A(x)`. -/
def lieDerivEndomorphism (V : E → E) (A : E → E →L[𝕜] E) (x : E) : E →L[𝕜] E :=
  fderiv 𝕜 A x (V x) + (A x).comp (fderiv 𝕜 V x) - (fderiv 𝕜 V x).comp (A x)

theorem lieDerivEndomorphismWithin_def (V : E → E) (A : E → E →L[𝕜] E) (s : Set E) (x : E) :
    lieDerivEndomorphismWithin V A s x = fderivWithin 𝕜 A s x (V x) +
      (A x).comp (fderivWithin 𝕜 V s x) - (fderivWithin 𝕜 V s x).comp (A x) := (rfl)

theorem lieDerivEndomorphism_def (V : E → E) (A : E → E →L[𝕜] E) (x : E) :
    lieDerivEndomorphism V A x =
      fderiv 𝕜 A x (V x) + (A x).comp (fderiv 𝕜 V x) - (fderiv 𝕜 V x).comp (A x) := (rfl)

@[simp]
theorem lieDerivEndomorphismWithin_univ (V : E → E) (A : E → E →L[𝕜] E) :
    lieDerivEndomorphismWithin V A univ = lieDerivEndomorphism V A := by
  ext x w; simp [lieDerivEndomorphismWithin_def, lieDerivEndomorphism_def]

/-- Pointwise evaluation of `lieDerivEndomorphismWithin` on a vector `w`. -/
theorem lieDerivEndomorphismWithin_apply (V : E → E) (A : E → E →L[𝕜] E) (s : Set E) (x w : E) :
    lieDerivEndomorphismWithin V A s x w = fderivWithin 𝕜 A s x (V x) w +
      A x (fderivWithin 𝕜 V s x w) - fderivWithin 𝕜 V s x (A x w) := (rfl)

/-- Pointwise evaluation of `lieDerivEndomorphism` on a vector `w`. -/
theorem lieDerivEndomorphism_apply (V : E → E) (A : E → E →L[𝕜] E) (x w : E) :
    lieDerivEndomorphism V A x w =
      fderiv 𝕜 A x (V x) w + A x (fderiv 𝕜 V x w) - fderiv 𝕜 V x (A x w) := (rfl)

/-! ### Algebraic properties and locality -/

@[simp]
theorem lieDerivEndomorphismWithin_zero (V : E → E) (s : Set E) (x : E) :
    lieDerivEndomorphismWithin V (0 : E → E →L[𝕜] E) s x = 0 := by
  ext w; simp [lieDerivEndomorphismWithin_apply]

@[simp]
theorem lieDerivEndomorphism_zero (V : E → E) :
    lieDerivEndomorphism V (0 : E → E →L[𝕜] E) = 0 := by
  rw [← lieDerivEndomorphismWithin_univ]; exact funext (lieDerivEndomorphismWithin_zero V univ)

@[simp]
theorem lieDerivEndomorphismWithin_zero_left (A : E → E →L[𝕜] E) (s : Set E) (x : E) :
    lieDerivEndomorphismWithin (0 : E → E) A s x = 0 := by
  ext w; simp [lieDerivEndomorphismWithin_apply]

@[simp]
theorem lieDerivEndomorphism_zero_left (A : E → E →L[𝕜] E) :
    lieDerivEndomorphism (0 : E → E) A = 0 := by
  rw [← lieDerivEndomorphismWithin_univ]; exact funext (lieDerivEndomorphismWithin_zero_left A univ)

/-- The Lie derivative of a constant endomorphism field `A₀` is the commutator `[A₀, DV]`. -/
theorem lieDerivEndomorphismWithin_const (V : E → E) (A₀ : E →L[𝕜] E) (s : Set E) (x : E) :
    lieDerivEndomorphismWithin V (fun _ ↦ A₀) s x =
      A₀.comp (fderivWithin 𝕜 V s x) - (fderivWithin 𝕜 V s x).comp A₀ := by
  ext w; simp [lieDerivEndomorphismWithin_apply]

/-- The Lie derivative of a constant endomorphism field `A₀` is the commutator `[A₀, DV]`. -/
theorem lieDerivEndomorphism_const (V : E → E) (A₀ : E →L[𝕜] E) (x : E) :
    lieDerivEndomorphism V (fun _ ↦ A₀) x = A₀.comp (fderiv 𝕜 V x) - (fderiv 𝕜 V x).comp A₀ := by
  simpa only [lieDerivEndomorphismWithin_univ, fderivWithin_univ] using
    lieDerivEndomorphismWithin_const V A₀ univ x

@[simp]
theorem lieDerivEndomorphismWithin_const_id (V : E → E) (s : Set E) (x : E) :
    lieDerivEndomorphismWithin V (fun _ ↦ ContinuousLinearMap.id 𝕜 E) s x = 0 := by
  ext w; simp [lieDerivEndomorphismWithin_const]

@[simp]
theorem lieDerivEndomorphism_const_id (V : E → E) (x : E) :
    lieDerivEndomorphism V (fun _ ↦ ContinuousLinearMap.id 𝕜 E) x = 0 := by
  ext w; simp [lieDerivEndomorphism_const]

theorem lieDerivEndomorphismWithin_add (hs : UniqueDiffWithinAt 𝕜 s x)
    (hA : DifferentiableWithinAt 𝕜 A s x) (hB : DifferentiableWithinAt 𝕜 B s x) :
    lieDerivEndomorphismWithin V (A + B) s x =
      lieDerivEndomorphismWithin V A s x + lieDerivEndomorphismWithin V B s x := by
  ext w
  simp only [lieDerivEndomorphismWithin_apply, fderivWithin_add hs hA hB, Pi.add_apply,
    add_apply, map_add]
  abel

theorem lieDerivEndomorphism_add (hA : DifferentiableAt 𝕜 A x) (hB : DifferentiableAt 𝕜 B x) :
    lieDerivEndomorphism V (A + B) x =
      lieDerivEndomorphism V A x + lieDerivEndomorphism V B x := by
  simpa only [lieDerivEndomorphismWithin_univ] using
    lieDerivEndomorphismWithin_add (V := V) uniqueDiffWithinAt_univ
      hA.differentiableWithinAt hB.differentiableWithinAt

theorem lieDerivEndomorphismWithin_neg (V : E → E) (A : E → E →L[𝕜] E)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivEndomorphismWithin V (-A) s x = -lieDerivEndomorphismWithin V A s x := by
  ext w; rw [lieDerivEndomorphismWithin_apply, fderivWithin_neg hs]
  simp only [Pi.neg_apply, neg_apply, map_neg, lieDerivEndomorphismWithin_apply]; abel

@[simp]
theorem lieDerivEndomorphism_neg (V : E → E) (A : E → E →L[𝕜] E) :
    lieDerivEndomorphism V (-A) = -lieDerivEndomorphism V A := by
  ext x w
  simp only [lieDerivEndomorphism_apply, fderiv_neg, Pi.neg_apply, neg_apply, map_neg]; abel

theorem lieDerivEndomorphismWithin_sub (hs : UniqueDiffWithinAt 𝕜 s x)
    (hA : DifferentiableWithinAt 𝕜 A s x) (hB : DifferentiableWithinAt 𝕜 B s x) :
    lieDerivEndomorphismWithin V (A - B) s x =
      lieDerivEndomorphismWithin V A s x - lieDerivEndomorphismWithin V B s x := by
  rw [sub_eq_add_neg, lieDerivEndomorphismWithin_add hs hA hB.neg,
    lieDerivEndomorphismWithin_neg V B hs, ← sub_eq_add_neg]

theorem lieDerivEndomorphism_sub (hA : DifferentiableAt 𝕜 A x) (hB : DifferentiableAt 𝕜 B x) :
    lieDerivEndomorphism V (A - B) x =
      lieDerivEndomorphism V A x - lieDerivEndomorphism V B x := by
  simpa only [lieDerivEndomorphismWithin_univ] using
    lieDerivEndomorphismWithin_sub (V := V) uniqueDiffWithinAt_univ
      hA.differentiableWithinAt hB.differentiableWithinAt

@[simp]
theorem lieDerivEndomorphismWithin_smul (c : 𝕜) (A : E → E →L[𝕜] E)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivEndomorphismWithin V (c • A) s x = c • lieDerivEndomorphismWithin V A s x := by
  ext w; rw [lieDerivEndomorphismWithin_apply, fderivWithin_const_smul_field (f := A) c hs]
  simp [lieDerivEndomorphismWithin_apply, smul_sub, smul_add]

@[simp]
theorem lieDerivEndomorphism_smul (c : 𝕜) (A : E → E →L[𝕜] E) :
    lieDerivEndomorphism V (c • A) = c • lieDerivEndomorphism V A := by
  ext x w; rw [lieDerivEndomorphism_apply, fderiv_const_smul_field (f := A) c]
  simp [lieDerivEndomorphism_apply, smul_sub, smul_add]

theorem lieDerivEndomorphism_add_left (hU : DifferentiableAt 𝕜 U x)
    (hV : DifferentiableAt 𝕜 V x) :
    lieDerivEndomorphism (U + V) A x =
      lieDerivEndomorphism U A x + lieDerivEndomorphism V A x := by
  ext w
  simp only [lieDerivEndomorphism_apply, fderiv_add hU hV, Pi.add_apply, add_apply, map_add]; abel

theorem lieDerivEndomorphism_neg_left (V : E → E) (A : E → E →L[𝕜] E) (x : E) :
    lieDerivEndomorphism (-V) A x = -lieDerivEndomorphism V A x := by
  ext w; simp only [lieDerivEndomorphism_apply, fderiv_neg, Pi.neg_apply, neg_apply, map_neg]; abel

theorem lieDerivEndomorphism_sub_left (hU : DifferentiableAt 𝕜 U x)
    (hV : DifferentiableAt 𝕜 V x) :
    lieDerivEndomorphism (U - V) A x =
      lieDerivEndomorphism U A x - lieDerivEndomorphism V A x := by
  rw [sub_eq_add_neg, lieDerivEndomorphism_add_left hU hV.neg,
    lieDerivEndomorphism_neg_left, ← sub_eq_add_neg]

theorem lieDerivEndomorphism_const_smul_left (c : 𝕜) (hV : DifferentiableAt 𝕜 V x) :
    lieDerivEndomorphism (c • V) A x = c • lieDerivEndomorphism V A x := by
  ext w
  simp only [lieDerivEndomorphism_apply, fderiv_const_smul hV, Pi.smul_apply,
    smul_apply, map_smul, smul_sub, smul_add]

theorem _root_.Filter.EventuallyEq.lieDerivEndomorphismWithin_eq_nhds
    (hV : V₁ =ᶠ[𝓝 x] V) (hA : A₁ =ᶠ[𝓝 x] A) :
    lieDerivEndomorphismWithin V₁ A₁ s x = lieDerivEndomorphismWithin V A s x := by
  have hVs :=
    (hV.filter_mono (nhdsWithin_le_nhds (s := s))).fderivWithin_eq (𝕜 := 𝕜) hV.self_of_nhds
  have hAs :=
    (hA.filter_mono (nhdsWithin_le_nhds (s := s))).fderivWithin_eq (𝕜 := 𝕜) hA.self_of_nhds
  simp only [lieDerivEndomorphismWithin_def, hV.self_of_nhds, hA.self_of_nhds, hVs, hAs]

theorem _root_.Filter.EventuallyEq.lieDerivEndomorphism_eq
    (hV : V₁ =ᶠ[𝓝 x] V) (hA : A₁ =ᶠ[𝓝 x] A) :
    lieDerivEndomorphism V₁ A₁ x = lieDerivEndomorphism V A x := by
  rw [← lieDerivEndomorphismWithin_univ, ← lieDerivEndomorphismWithin_univ,
    hV.lieDerivEndomorphismWithin_eq_nhds hA]

protected theorem _root_.Filter.EventuallyEq.lieDerivEndomorphism
    (hV : V₁ =ᶠ[𝓝 x] V) (hA : A₁ =ᶠ[𝓝 x] A) :
    lieDerivEndomorphism V₁ A₁ =ᶠ[𝓝 x] lieDerivEndomorphism V A := by
  filter_upwards [hV.eventuallyEq_nhds, hA.eventuallyEq_nhds] with y hVy hAy
  exact hVy.lieDerivEndomorphism_eq hAy

/-- If `V` and `A` are `C^n` at `x` with `m + 1 ≤ n`, then `lieDerivEndomorphism V A` is `C^m` at
`x`. -/
theorem contDiffAt_lieDerivEndomorphism {n m : ℕ∞ω} (hV : ContDiffAt 𝕜 n V x)
    (hA : ContDiffAt 𝕜 n A x) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (lieDerivEndomorphism V A) x := by
  have hm : m ≤ n := le_self_add.trans hmn
  exact (((hA.fderiv_right hmn).clm_apply (hV.of_le hm)).add
    ((hA.of_le hm).clm_comp (hV.fderiv_right hmn))).sub
      ((hV.fderiv_right hmn).clm_comp (hA.of_le hm))

/-! ### Bracket formula and composition derivation rule -/

/-- **Bracket formula** for `lieDerivEndomorphismWithin`: evaluated on a vector field `W`,
`(L_V A)(W) = [V, A W] - A [V, W]`. -/
theorem lieDerivEndomorphismWithin_apply_vectorField (hs : UniqueDiffWithinAt 𝕜 s x)
    (hA : DifferentiableWithinAt 𝕜 A s x) (hW : DifferentiableWithinAt 𝕜 W s x) :
    lieDerivEndomorphismWithin V A s x (W x) =
      lieBracketWithin 𝕜 V (fun y ↦ A y (W y)) s x - A x (lieBracketWithin 𝕜 V W s x) := by
  simp only [lieBracketWithin_eq, fderivWithin_clm_apply hs hA hW, lieDerivEndomorphismWithin_apply,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, map_sub]
  abel

/-- **Bracket formula** for `lieDerivEndomorphism`: evaluated on a vector field `W`,
`(L_V A)(W) = [V, A W] - A [V, W]`. -/
theorem lieDerivEndomorphism_apply_vectorField
    (hA : DifferentiableAt 𝕜 A x) (hW : DifferentiableAt 𝕜 W x) :
    lieDerivEndomorphism V A x (W x) =
      lieBracket 𝕜 V (fun y ↦ A y (W y)) x - A x (lieBracket 𝕜 V W x) := by
  simpa only [lieDerivEndomorphismWithin_univ, lieBracketWithin_univ] using
    lieDerivEndomorphismWithin_apply_vectorField (V := V) uniqueDiffWithinAt_univ
      hA.differentiableWithinAt hW.differentiableWithinAt

/-- Specializing `lieDerivEndomorphism_apply_vectorField` to a constant vector field expresses
`(L_V A)(x) w` purely in terms of vector-field brackets. -/
theorem lieDerivEndomorphism_apply_eq_lieBracket (hA : DifferentiableAt 𝕜 A x) (w : E) :
    lieDerivEndomorphism V A x w =
      lieBracket 𝕜 V (fun y ↦ A y w) x - A x (lieBracket 𝕜 V (fun _ ↦ w) x) :=
  lieDerivEndomorphism_apply_vectorField hA (differentiableAt_const w)

/-- **Derivation rule** on composition within a set:
`L_V (A ∘ B) = (L_V A) ∘ B + A ∘ (L_V B)`. No differentiability of `V` is required. -/
theorem lieDerivEndomorphismWithin_comp (hs : UniqueDiffWithinAt 𝕜 s x)
    (hA : DifferentiableWithinAt 𝕜 A s x) (hB : DifferentiableWithinAt 𝕜 B s x) :
    lieDerivEndomorphismWithin V (fun y ↦ (A y).comp (B y)) s x =
      (lieDerivEndomorphismWithin V A s x).comp (B x) +
        (A x).comp (lieDerivEndomorphismWithin V B s x) := by
  have hd := congrArg (· (V x))
    ((hA.hasFDerivWithinAt.clm_comp hB.hasFDerivWithinAt).fderivWithin hs)
  ext w
  simp only [lieDerivEndomorphismWithin_def, hd, add_apply, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, map_add, map_sub]
  abel

/-- **Derivation rule** on composition: `L_V (A ∘ B) = (L_V A) ∘ B + A ∘ (L_V B)`. -/
theorem lieDerivEndomorphism_comp (hA : DifferentiableAt 𝕜 A x) (hB : DifferentiableAt 𝕜 B x) :
    lieDerivEndomorphism V (fun y ↦ (A y).comp (B y)) x =
      (lieDerivEndomorphism V A x).comp (B x) + (A x).comp (lieDerivEndomorphism V B x) := by
  simpa only [lieDerivEndomorphismWithin_univ] using
    lieDerivEndomorphismWithin_comp (V := V) uniqueDiffWithinAt_univ
      hA.differentiableWithinAt hB.differentiableWithinAt

/-- If `A² = -1` on a neighborhood of `x` and `A` is differentiable at `x`, then `L_V A (x)`
anticommutes with `A x`. -/
theorem lieDerivEndomorphism_comp_add_comp_eq_zero (hA : DifferentiableAt 𝕜 A x)
    (hsq : (fun y ↦ (A y).comp (A y)) =ᶠ[𝓝 x] fun _ ↦ -ContinuousLinearMap.id 𝕜 E) :
    (lieDerivEndomorphism V A x).comp (A x) + (A x).comp (lieDerivEndomorphism V A x) = 0 := by
  have h0 : lieDerivEndomorphism V (fun y ↦ (A y).comp (A y)) x = 0 := by
    rw [(Filter.EventuallyEq.refl (𝓝 x) V).lieDerivEndomorphism_eq hsq, ← Pi.neg_def,
      lieDerivEndomorphism_neg, Pi.neg_apply, lieDerivEndomorphism_const_id, neg_zero]
  rwa [lieDerivEndomorphism_comp hA hA] at h0

/-! ### Commutator identity and source-bracket sign comparison -/

/-- **Commutator identity** for Mathlib's Lie bracket `[U, V] = DV · U - DU · V`:
for `C²` vector fields `U`, `V` and endomorphism field `A` at `x`,
`L_{[U, V]} A = L_U (L_V A) - L_V (L_U A)`. -/
theorem lieDerivEndomorphism_lieBracket {n : ℕ∞ω} (hn : minSmoothness 𝕜 2 ≤ n)
    (hU : ContDiffAt 𝕜 n U x) (hV : ContDiffAt 𝕜 n V x) (hA : ContDiffAt 𝕜 n A x) :
    lieDerivEndomorphism (lieBracket 𝕜 U V) A x =
      lieDerivEndomorphism U (lieDerivEndomorphism V A) x -
        lieDerivEndomorphism V (lieDerivEndomorphism U A) x := by
  have h1n : (1 : ℕ∞ω) ≤ n := (one_le_two.trans le_minSmoothness).trans hn
  have h11n : (1 + 1 : ℕ∞ω) ≤ n := (by norm_cast : (1 + 1 : ℕ∞ω) = 2).trans_le
    (le_minSmoothness.trans hn)
  have hAx : DifferentiableAt 𝕜 A x := (hA.of_le h1n).differentiableAt one_ne_zero
  have hA_ev : ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 A y :=
    ((hA.of_le h1n).eventually (by simp)).mono fun y hy ↦ hy.differentiableAt one_ne_zero
  have hLA (Z : E → E) (hZ : ContDiffAt 𝕜 n Z x) :
      DifferentiableAt 𝕜 (lieDerivEndomorphism Z A) x :=
    (contDiffAt_lieDerivEndomorphism hZ hA h11n).differentiableAt one_ne_zero
  ext w
  have hc : ContDiffAt 𝕜 n (fun _ : E ↦ w) x := contDiffAt_const
  have hbrZ (Z : E → E) : lieBracket 𝕜 Z (fun y ↦ A y w) =ᶠ[𝓝 x]
      ((fun y ↦ lieDerivEndomorphism Z A y w) + fun y ↦ A y (lieBracket 𝕜 Z (fun _ ↦ w) y)) :=
    hA_ev.mono fun y hy ↦ by
      simp only [Pi.add_apply, lieDerivEndomorphism_apply_eq_lieBracket hy w, sub_add_cancel]
  have hZ_diff (Z : E → E) (hZ : ContDiffAt 𝕜 n Z x) :
      DifferentiableAt 𝕜 (lieBracket 𝕜 Z (fun _ ↦ w)) x := by
    rw [show lieBracket 𝕜 Z (fun _ ↦ w) = fun y ↦ -(fderiv 𝕜 Z y w) by ext y; simp [lieBracket_eq]]
    exact (((hZ.fderiv_right h11n).clm_apply contDiffAt_const).differentiableAt one_ne_zero).neg
  have hstep {Y Z : E → E} (hZ : ContDiffAt 𝕜 n Z x) :
      lieBracket 𝕜 Y (lieBracket 𝕜 Z (fun y ↦ A y w)) x =
        lieDerivEndomorphism Y (lieDerivEndomorphism Z A) x w +
          lieDerivEndomorphism Z A x (lieBracket 𝕜 Y (fun _ ↦ w) x) +
          lieDerivEndomorphism Y A x (lieBracket 𝕜 Z (fun _ ↦ w) x) +
          A x (lieBracket 𝕜 Y (lieBracket 𝕜 Z (fun _ ↦ w)) x) := by
    rw [(Filter.EventuallyEq.refl (𝓝 x) Y).lieBracket_vectorField_eq (hbrZ Z),
      lieBracket_add_right ((hLA Z hZ).clm_apply (differentiableAt_const w))
        (hAx.clm_apply (hZ_diff Z hZ)),
      eq_add_of_sub_eq (lieDerivEndomorphism_apply_eq_lieBracket (V := Y) (hLA Z hZ) w).symm,
      eq_add_of_sub_eq (lieDerivEndomorphism_apply_vectorField (V := Y) hAx (hZ_diff Z hZ)).symm]
    abel
  have hJ_Aw := eq_sub_of_add_eq
    (VectorField.leibniz_identity_lieBracket hn hU hV (hA.clm_apply hc)).symm
  have hJ_c := eq_sub_of_add_eq (VectorField.leibniz_identity_lieBracket hn hU hV hc).symm
  simp only [sub_apply]
  rw [lieDerivEndomorphism_apply_eq_lieBracket (V := lieBracket 𝕜 U V) hAx w,
    hJ_Aw, hJ_c, hstep hV, hstep hU, map_sub]
  abel

/-- **Source-bracket commutator identity**: for the opposite bracket
`[U, V]_RS(y) = DU(y)(V y) - DV(y)(U y) = -lieBracket 𝕜 U V y` used by Robbin–Salamon,
`L_{[U, V]_RS} A = L_V (L_U A) - L_U (L_V A)`. -/
theorem lieDerivEndomorphism_fderiv_sub_fderiv {n : ℕ∞ω} (hn : minSmoothness 𝕜 2 ≤ n)
    (hU : ContDiffAt 𝕜 n U x) (hV : ContDiffAt 𝕜 n V x) (hA : ContDiffAt 𝕜 n A x) :
    lieDerivEndomorphism (fun y ↦ fderiv 𝕜 U y (V y) - fderiv 𝕜 V y (U y)) A x =
      lieDerivEndomorphism V (lieDerivEndomorphism U A) x -
        lieDerivEndomorphism U (lieDerivEndomorphism V A) x := by
  rw [show (fun y ↦ fderiv 𝕜 U y (V y) - fderiv 𝕜 V y (U y)) = -lieBracket 𝕜 U V by
      ext y; simp [lieBracket_eq],
    lieDerivEndomorphism_neg_left, lieDerivEndomorphism_lieBracket hn hU hV hA, neg_sub]

/-! ### Nijenhuis–Lie-derivative identities -/

/-- **Nijenhuis–Lie-derivative identity**: if `A x` squares to `-1`, then for every differentiable
vector field `X`, the derivative `DX(x)` cancels out of `(L_{A X} A)(x) w - A x ((L_X A)(x) w)`,
leaving the pointwise Nijenhuis expression of `A` on `(X x, w)`. -/
theorem lieDerivEndomorphism_apply_sub_apply (hA : DifferentiableAt 𝕜 A x)
    (hX : DifferentiableAt 𝕜 X x) (hsq : ∀ u, A x (A x u) = -u) (w : E) :
    lieDerivEndomorphism (fun y ↦ A y (X y)) A x w - A x (lieDerivEndomorphism X A x w) =
      fderiv 𝕜 A x (A x (X x)) w - fderiv 𝕜 A x (A x w) (X x) +
        A x (fderiv 𝕜 A x w (X x)) - A x (fderiv 𝕜 A x (X x) w) := by
  have hd : fderiv 𝕜 (fun y ↦ A y (X y)) x =
      (A x).comp (fderiv 𝕜 X x) + (fderiv 𝕜 A x).flip (X x) :=
    fderiv_clm_apply hA hX
  simp only [lieDerivEndomorphism_apply, hd, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    map_add, map_sub, hsq]
  abel

/-- Pointwise vector-field bracket formula for the Nijenhuis expression on a normed space: when
`A x` squares to `-1`, the derivatives of `U` and `W` cancel out of
`[A U, A W] - [U, W] - A [A U, W] - A [U, A W]`. -/
theorem lieBracket_apply_sub_lieBracket_eq {U W : E → E} (hA : DifferentiableAt 𝕜 A x)
    (hU : DifferentiableAt 𝕜 U x) (hW : DifferentiableAt 𝕜 W x) (hsq : ∀ u, A x (A x u) = -u) :
    lieBracket 𝕜 (fun y ↦ A y (U y)) (fun y ↦ A y (W y)) x - lieBracket 𝕜 U W x -
        A x (lieBracket 𝕜 (fun y ↦ A y (U y)) W x) -
        A x (lieBracket 𝕜 U (fun y ↦ A y (W y)) x) =
      fderiv 𝕜 A x (A x (U x)) (W x) - fderiv 𝕜 A x (A x (W x)) (U x) +
        A x (fderiv 𝕜 A x (W x) (U x)) - A x (fderiv 𝕜 A x (U x) (W x)) := by
  have hdU := fderiv_clm_apply hA hU
  have hdW := fderiv_clm_apply hA hW
  simp only [lieBracket_eq, hdU, hdW, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, map_add, map_sub, hsq]
  abel

end TauCeti
