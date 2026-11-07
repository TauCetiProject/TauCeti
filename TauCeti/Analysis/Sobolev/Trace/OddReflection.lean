/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Reflection
public import TauCeti.Analysis.Sobolev.W1p.Zero
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry

/-!
# Odd reflection of second-order Sobolev functions across a hyperplane

Let `H = {x | a < x.fst}` be a half-space of the Euclidean product `ℝ × E`, let
`ρ (t, y) = (2a - t, y)` be the reflection in its boundary hyperplane `{a} × E`, and let
`R (s, z) = (-s, z)` be the linear part of `ρ`. For every `1 ≤ p ≤ ∞`, this file proves that the
odd reflection of a function `u ∈ W^{2,p}(H)` whose first-order part lies in `W^{1,p}_0(H)`,

`v = u` on `H`, `v = -u ∘ ρ` on the other side,

lies in `W^{2,p}(ℝ × E)`, with weak Hessian `D²u` on `H` and `-R ∘ D²u (ρ x) ∘ R` on the other
side (`TauCeti.Wkp.exists_value_ae_eq_sub_comp_normalReflection`). The zero boundary condition
cannot be dropped: the odd reflection of a function with nonzero trace jumps across the
hyperplane.

Since `R` is an orthogonal involution, the Laplacian of `v` is the odd reflection of the
Laplacian of `u`, and `D²v` has the same `Lᵖ` norm on `H` as `D²u`. This is how whole-space
estimates for strong solutions of `Δu = f` transfer to solutions on a half-space vanishing on the
boundary hyperplane.

## The argument

The zero extension of the first-order part of `u` is a Sobolev function on the whole space
(`TauCeti.W1p0.extendByZeroL`), and so is its composition with `ρ`
(`TauCeti.HasWeakFDerivOn.comp_normalReflection`); their difference is `v`. Its derivative in the
normal direction `ν = (1, 0)` is the even reflection of `∂_ν u`, a Sobolev function by
`TauCeti.HasWeakFDerivOn.add_comp_normalReflection`. Its derivative in a tangential direction
`τ` is the odd reflection of `∂_τ u`. Tangential derivatives of an odd reflection need no
boundary condition (`TauCeti.HasWeakFDerivOn.hasWeakLineDerivOn_sub_comp_normalReflection`), and
the normal derivative of `∂_τ v` is `∂_τ ∂_ν v` because weak derivatives commute
(`TauCeti.HasWeakLineDerivOn.comm`). So every first derivative of `v` lies in `W^{1,p}`, and
`v ∈ W^{2,p}` (`TauCeti.Wkp.exists_value_eq_iff_forall_exists_hasWeakLineDerivOn`). Uniqueness of
weak derivatives identifies the entries of `D²v` along an orthonormal basis adapted to the
hyperplane, using the symmetry of the weak Hessian of `u`
(`TauCeti.Wkp.inner_iteratedGradient_one_apply_ae_eq`).

## Main declarations

* `TauCeti.Wkp.exists_value_ae_eq_sub_comp_normalReflection`: the odd reflection of a function
  in `W^{2,p}(H)` with first-order part in `W^{1,p}_0(H)` lies in `W^{2,p}(ℝ × E)`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Lemma 9.2 (extension by reflection across a hyperplane).
* L. C. Evans, *Partial Differential Equations*, §5.4 (extension by reflection).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Construction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem ae_restrict_top :
    ae ((volume : Measure (WithLp 2 (ℝ × E))).restrict ((⊤ : Opens (WithLp 2 (ℝ × E))) :
      Set (WithLp 2 (ℝ × E)))) = ae volume := by
  simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- Splitting a direction `v` into its normal and tangential parts, the pairing of `w - R w'`
with `v` is `v.fst (⟪w, ν⟫ + ⟪w', ν⟫) + (⟪w, τ⟫ - ⟪w', τ⟫)`, where `ν = (1, 0)` and
`τ = (0, v.snd)`. -/
private theorem inner_sub_normalLinearReflection_eq (w w' v : WithLp 2 (ℝ × E)) :
    ⟪w - normalLinearReflection E w', v⟫_ℝ =
      v.fst * (⟪w, WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ +
          ⟪w', WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ) +
        (⟪w, WithLp.toLp 2 ((0 : ℝ), v.snd)⟫_ℝ - ⟪w', WithLp.toLp 2 ((0 : ℝ), v.snd)⟫_ℝ) := by
  obtain ⟨⟨s, y⟩⟩ := w
  obtain ⟨⟨s', y'⟩⟩ := w'
  obtain ⟨⟨t, z⟩⟩ := v
  simp [WithLp.prod_inner_apply, inner_sub_left, ← WithLp.toLp_sub]

/-- The odd reflection `f - f ∘ ρ` of a function `f` with weak gradient `G` has weak gradient
`G - R (G ∘ ρ)`. -/
private theorem hasWeakFDerivOn_sub_comp_normalReflection_innerSL {a : ℝ}
    {f : WithLp 2 (ℝ × E) → ℝ} {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    (hfG : HasWeakFDerivOn volume ⊤ f fun x => innerSL ℝ (G x)) :
    HasWeakFDerivOn volume ⊤ (fun x => f x - f (normalReflection E a x))
      fun x => innerSL ℝ (G x - normalLinearReflection E (G (normalReflection E a x))) :=
  (hfG.sub hfG.comp_normalReflection).congr_ae_deriv
    (Eventually.of_forall fun x => by simp only [Pi.sub_apply, map_sub])

/-- The normal component of the gradient of an odd reflection: the sum of `⟪G, ν⟫` and its
reflection has weak gradient given by the even reflection of `D ν`. -/
private theorem hasWeakFDerivOn_inner_normal_add_comp_normalReflection {a : ℝ}
    {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    {D : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hG : MemLp G p volume) (hD : ∀ c, MemLp (fun x => D x c) p volume)
    (hG0 : ∀ x ∉ normalHalfSpace (E := E) a, G x = 0)
    (hD0 : ∀ x ∉ normalHalfSpace (E := E) a, D x = 0)
    (hGD : ∀ c, HasWeakFDerivOn volume (normalHalfSpace a) (fun x => ⟪G x, c⟫_ℝ)
      fun x => innerSL ℝ (D x c)) :
    HasWeakFDerivOn volume ⊤
      (fun x => ⟪G x, WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ +
        ⟪G (normalReflection E a x), WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ)
      fun x => innerSL ℝ (D x (WithLp.toLp 2 ((1 : ℝ), (0 : E))) +
        normalLinearReflection E (D (normalReflection E a x) (WithLp.toLp 2 ((1 : ℝ), (0 : E))))) :=
  (hGD _).add_comp_normalReflection ((hG.inner_const _).locallyIntegrable Fact.out)
    ((hD _).locallyIntegrable Fact.out) (fun x hx => by simp [hG0 x hx])
    (fun x hx => by simp [hD0 x hx])

/-- A tangential component of the gradient of an odd reflection is itself an odd reflection, and
its tangential derivatives are odd reflections of those of `D`. -/
private theorem hasWeakLineDerivOn_inner_tangent_sub_comp_normalReflection {a : ℝ}
    {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    {D : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hG : MemLp G p volume) (hD : ∀ c, MemLp (fun x => D x c) p volume)
    (hG0 : ∀ x ∉ normalHalfSpace (E := E) a, G x = 0)
    (hD0 : ∀ x ∉ normalHalfSpace (E := E) a, D x = 0)
    (hGD : ∀ c, HasWeakFDerivOn volume (normalHalfSpace a) (fun x => ⟪G x, c⟫_ℝ)
      fun x => innerSL ℝ (D x c)) (y z : E) :
    HasWeakLineDerivOn volume ⊤
      (fun x => ⟪G x, WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ -
        ⟪G (normalReflection E a x), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ)
      (fun x => ⟪D x (WithLp.toLp 2 ((0 : ℝ), y)) -
        normalLinearReflection E (D (normalReflection E a x) (WithLp.toLp 2 ((0 : ℝ), y))),
          WithLp.toLp 2 ((0 : ℝ), z)⟫_ℝ) (WithLp.toLp 2 ((0 : ℝ), z)) :=
  (hGD _).hasWeakLineDerivOn_sub_comp_normalReflection
    ((hG.inner_const _).locallyIntegrable Fact.out) ((hD _).locallyIntegrable Fact.out)
    (fun x hx => by simp [hG0 x hx]) (fun x hx => by simp [hD0 x hx]) rfl

/-- The normal derivative of a tangential component of the gradient of an odd reflection is the
even reflection of `D ν` paired with the tangential direction: weak derivatives commute. -/
private theorem hasWeakLineDerivOn_inner_tangent_sub_comp_normalReflection_normal {a : ℝ}
    {f : WithLp 2 (ℝ × E) → ℝ} {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    {D : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (h2 : HasWeakFDerivOn volume ⊤ (fun x => f x - f (normalReflection E a x))
      fun x => innerSL ℝ (G x - normalLinearReflection E (G (normalReflection E a x))))
    (h4 : HasWeakFDerivOn volume ⊤
      (fun x => ⟪G x, WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ +
        ⟪G (normalReflection E a x), WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ)
      fun x => innerSL ℝ (D x (WithLp.toLp 2 ((1 : ℝ), (0 : E))) +
        normalLinearReflection E (D (normalReflection E a x) (WithLp.toLp 2 ((1 : ℝ), (0 : E))))))
    (y : E) :
    HasWeakLineDerivOn volume ⊤
      (fun x => ⟪G x, WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ -
        ⟪G (normalReflection E a x), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ)
      (fun x => ⟪D x (WithLp.toLp 2 ((1 : ℝ), (0 : E))) +
        normalLinearReflection E (D (normalReflection E a x) (WithLp.toLp 2 ((1 : ℝ), (0 : E)))),
          WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ) (WithLp.toLp 2 ((1 : ℝ), (0 : E))) := by
  have h₁ := (h2.hasWeakLineDerivOn (WithLp.toLp 2 ((1 : ℝ), (0 : E)))).congr_ae_deriv
    (Eventually.of_forall fun x =>
      (innerSL_apply_apply ℝ _ _).trans (inner_sub_normalLinearReflection_normal _ _))
  have h₂ := (h2.hasWeakLineDerivOn (WithLp.toLp 2 ((0 : ℝ), y))).congr_ae_deriv
    (Eventually.of_forall fun x =>
      (innerSL_apply_apply ℝ _ _).trans (inner_sub_normalLinearReflection_tangent _ _ y))
  simpa only [innerSL_apply_apply] using
    h₁.comm (h4.hasWeakLineDerivOn (WithLp.toLp 2 ((0 : ℝ), y))) h₂

/-- The normal derivative of the odd reflection's gradient pairing: the even reflection of
`⟪G, ν⟫` is a first-order Sobolev function. -/
private theorem exists_wkp_one_value_ae_eq_inner_normal_add_comp_normalReflection {a : ℝ}
    {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    {D : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hG : MemLp G p volume) (hD : ∀ c, MemLp (fun x => D x c) p volume)
    (h4 : HasWeakFDerivOn volume ⊤
      (fun x => ⟪G x, WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ +
        ⟪G (normalReflection E a x), WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ)
      fun x => innerSL ℝ (D x (WithLp.toLp 2 ((1 : ℝ), (0 : E))) +
        normalLinearReflection E (D (normalReflection E a x) (WithLp.toLp 2 ((1 : ℝ), (0 : E)))))) :
    ∃ N : Wkp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p 1,
      Wkp.value 1 N =ᵐ[volume] fun x => ⟪G x, WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ +
        ⟪G (normalReflection E a x), WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ := by
  have hρ := measurePreserving_normalReflection (E := E) a
  have hρD : MemLp (fun x => normalLinearReflection E (D (normalReflection E a x)
      (WithLp.toLp 2 ((1 : ℝ), (0 : E))))) p volume :=
    (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)).comp_memLp'
      ((hD _).comp_measurePreserving hρ)
  have h := Wkp.exists_value_one_ae_eq_of_forall_hasWeakLineDerivOn
    (w := fun x => ⟪G x, WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ +
      ⟪G (normalReflection E a x), WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ)
    (((hG.inner_const _).add ((hG.inner_const _).comp_measurePreserving hρ)).restrict _)
    (fun v x => ⟪D x (WithLp.toLp 2 ((1 : ℝ), (0 : E))) +
      normalLinearReflection E (D (normalReflection E a x)
        (WithLp.toLp 2 ((1 : ℝ), (0 : E)))), v⟫_ℝ)
    (fun v => (((hD _).add hρD).inner_const v).restrict _) fun v => by
      simpa only [innerSL_apply_apply] using h4.hasWeakLineDerivOn v
  rw [ae_restrict_top] at h
  exact h

/-- The tangential components of the gradient of an odd reflection are first-order Sobolev
functions. -/
private theorem exists_wkp_one_value_ae_eq_inner_tangent_sub_comp_normalReflection {a : ℝ}
    {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    {D : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hG : MemLp G p volume) (hD : ∀ c, MemLp (fun x => D x c) p volume)
    (h5 : ∀ y z : E, HasWeakLineDerivOn volume ⊤
      (fun x => ⟪G x, WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ -
        ⟪G (normalReflection E a x), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ)
      (fun x => ⟪D x (WithLp.toLp 2 ((0 : ℝ), y)) -
        normalLinearReflection E (D (normalReflection E a x) (WithLp.toLp 2 ((0 : ℝ), y))),
          WithLp.toLp 2 ((0 : ℝ), z)⟫_ℝ) (WithLp.toLp 2 ((0 : ℝ), z)))
    (h6 : ∀ y : E, HasWeakLineDerivOn volume ⊤
      (fun x => ⟪G x, WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ -
        ⟪G (normalReflection E a x), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ)
      (fun x => ⟪D x (WithLp.toLp 2 ((1 : ℝ), (0 : E))) +
        normalLinearReflection E (D (normalReflection E a x) (WithLp.toLp 2 ((1 : ℝ), (0 : E)))),
          WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ) (WithLp.toLp 2 ((1 : ℝ), (0 : E)))) (y : E) :
    ∃ T : Wkp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p 1,
      Wkp.value 1 T =ᵐ[volume] fun x => ⟪G x, WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ -
        ⟪G (normalReflection E a x), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ := by
  have hρ := measurePreserving_normalReflection (E := E) a
  have hρD (c : WithLp 2 (ℝ × E)) : MemLp (fun x => normalLinearReflection E
      (D (normalReflection E a x) c)) p volume :=
    (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)).comp_memLp'
      ((hD c).comp_measurePreserving hρ)
  have hsplit (v : WithLp 2 (ℝ × E)) :
      v.fst • WithLp.toLp 2 ((1 : ℝ), (0 : E)) + WithLp.toLp 2 ((0 : ℝ), v.snd) = v := by
    cases v; simp [← WithLp.toLp_smul, ← WithLp.toLp_add]
  have h := Wkp.exists_value_one_ae_eq_of_forall_hasWeakLineDerivOn
    (w := fun x => ⟪G x, WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ -
      ⟪G (normalReflection E a x), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ)
    (((hG.inner_const _).sub ((hG.inner_const _).comp_measurePreserving hρ)).restrict _)
    (fun v x => v.fst * ⟪D x (WithLp.toLp 2 ((1 : ℝ), (0 : E))) +
        normalLinearReflection E (D (normalReflection E a x) (WithLp.toLp 2 ((1 : ℝ), (0 : E)))),
          WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ +
      ⟪D x (WithLp.toLp 2 ((0 : ℝ), y)) -
        normalLinearReflection E (D (normalReflection E a x) (WithLp.toLp 2 ((0 : ℝ), y))),
          WithLp.toLp 2 ((0 : ℝ), v.snd)⟫_ℝ)
    (fun v => ((((hD _).add (hρD _)).inner_const _).const_mul v.fst).add
      (((hD _).sub (hρD _)).inner_const _) |>.restrict _) fun v => by
      have h := ((h6 y).smul_direction v.fst).add_direction (h5 y v.snd)
      rw [hsplit v] at h
      exact h
  rw [ae_restrict_top] at h
  exact h

/-- The odd reflection `f - f ∘ ρ` is the value of an element `W` of `W^{2,p}` whenever the
components of its gradient `G - R (G ∘ ρ)` are the values of first-order Sobolev functions, namely
`N` in the normal direction and `T y` in the tangential directions. Its weak gradient is then
`G - R (G ∘ ρ)`. -/
private theorem exists_wkp_two_value_ae_eq_sub_comp_normalReflection {a : ℝ}
    {f : WithLp 2 (ℝ × E) → ℝ} {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    (hf : MemLp f p volume)
    (h2 : HasWeakFDerivOn volume ⊤ (fun x => f x - f (normalReflection E a x))
      fun x => innerSL ℝ (G x - normalLinearReflection E (G (normalReflection E a x))))
    (N : Wkp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p 1)
    (T : E → Wkp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p 1)
    (hN : Wkp.value 1 N =ᵐ[volume] fun x => ⟪G x, WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ +
      ⟪G (normalReflection E a x), WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ)
    (hT : ∀ y, Wkp.value 1 (T y) =ᵐ[volume] fun x => ⟪G x, WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ -
      ⟪G (normalReflection E a x), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ) :
    ∃ W : Wkp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p 2,
      Wkp.value 2 W =ᵐ[volume] (fun x => f x - f (normalReflection E a x)) ∧
      ∀ᵐ x ∂volume, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 W) x =
        G x - normalLinearReflection E (G (normalReflection E a x)) := by
  have hρ := measurePreserving_normalReflection (E := E) a
  obtain ⟨W, hW⟩ := Wkp.exists_value_ae_eq_of_forall_hasWeakLineDerivOn 1
    ((hf.sub (hf.comp_measurePreserving hρ)).restrict _)
    (fun v => v.fst • N + T v.snd) fun v => by
      refine (h2.hasWeakLineDerivOn v).congr_ae_deriv ?_
      rw [ae_restrict_top]
      have hadd := Lp.coeFn_add (v.fst • Wkp.value 1 N) (Wkp.value 1 (T v.snd))
      have hsmul := Lp.coeFn_smul v.fst (Wkp.value 1 N)
      rw [ae_restrict_top] at hadd hsmul
      filter_upwards [hN, hT v.snd, hadd, hsmul] with x h1 h2 h3 h4
      rw [Wkp.value_add, Wkp.value_smul, h3, Pi.add_apply, h4, Pi.smul_apply, h1, h2,
        innerSL_apply_apply, inner_sub_normalLinearReflection_eq, smul_eq_mul]
  rw [ae_restrict_top] at hW
  refine ⟨W, hW, ?_⟩
  have hval : Wkp.value 1 (Wkp.lowerOrder 1 W) =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict
      ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E)))]
      fun x => f x - f (normalReflection E a x) := by
    rw [ae_restrict_top, ← Wkp.value_succ]
    exact hW
  have h := ((Wkp.hasWeakFDerivOn_value (Wkp.lowerOrder 1 W)).congr_ae hval).ae_eq h2
  rw [ae_restrict_top] at h
  filter_upwards [h] with x hx
  exact ext_inner_right ℝ fun v => by
    simpa only [innerSL_apply_apply] using DFunLike.congr_fun hx v

/-- Each entry of the weak Hessian of `W` is a weak derivative of a component of its weak
gradient `G - R (G ∘ ρ)`. -/
private theorem hasWeakLineDerivOn_inner_iteratedGradient_one {a : ℝ}
    {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    (W : Wkp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p 2)
    (hg : ∀ᵐ x ∂volume, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 W) x =
      G x - normalLinearReflection E (G (normalReflection E a x)))
    (c v : WithLp 2 (ℝ × E)) :
    HasWeakLineDerivOn volume ⊤
      (fun x => ⟪G x - normalLinearReflection E (G (normalReflection E a x)), c⟫_ℝ)
      (fun x => ⟪Wkp.iteratedGradient 1 W x v, c⟫_ℝ) v := by
  have h : HasWeakLineDerivOn volume ⊤
      (fun x => ⟪Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 W) x, c⟫_ℝ)
      (fun x => ⟪Wkp.iteratedGradient 1 W x v, c⟫_ℝ) v := by
    simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm c] using
      ((Wkp.hasWeakFDerivOn_iteratedGradient 0 W).clm_comp (innerSL ℝ c)).hasWeakLineDerivOn v
  refine h.congr_ae ?_
  rw [ae_restrict_top]
  filter_upwards [hg] with x hx
  rw [hx]

/-- The normal-direction entries of the weak Hessian of the odd reflection. -/
private theorem ae_inner_iteratedGradient_normal_eq {a : ℝ}
    {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    {D : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    {Φ : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (h4 : HasWeakFDerivOn volume ⊤
      (fun x => ⟪G x, WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ +
        ⟪G (normalReflection E a x), WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ)
      fun x => innerSL ℝ (D x (WithLp.toLp 2 ((1 : ℝ), (0 : E))) +
        normalLinearReflection E (D (normalReflection E a x) (WithLp.toLp 2 ((1 : ℝ), (0 : E))))))
    (hsymm : ∀ v c, ∀ᵐ x, ⟪D x v, c⟫_ℝ = ⟪D x c, v⟫_ℝ)
    (hcomp : ∀ v, HasWeakLineDerivOn volume ⊤
      (fun x => ⟪G x - normalLinearReflection E (G (normalReflection E a x)),
        WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ) (fun x => ⟪Φ x v, WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ)
        v)
    (v : WithLp 2 (ℝ × E)) :
    ∀ᵐ x ∂volume, ⟪Φ x v, WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ =
      ⟪(D x - (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
        D (normalReflection E a x) ∘L
          (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))) v,
        WithLp.toLp 2 ((1 : ℝ), (0 : E))⟫_ℝ := by
  have hρ := measurePreserving_normalReflection (E := E) a
  have hae := ((hcomp v).congr_ae (Eventually.of_forall fun x =>
    inner_sub_normalLinearReflection_normal (G x) (G (normalReflection E a x)))).ae_eq
      (h4.hasWeakLineDerivOn v)
  rw [ae_restrict_top] at hae
  filter_upwards [hae, hsymm v (WithLp.toLp 2 ((1 : ℝ), (0 : E))),
    hρ.quasiMeasurePreserving.ae
      (hsymm (normalLinearReflection E v) (WithLp.toLp 2 ((1 : ℝ), (0 : E))))]
    with x h1 h2 h3
  rw [h1]
  simp only [innerSL_apply_apply, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    inner_add_left, inner_sub_left, inner_normalLinearReflection_left_eq_right,
    normalLinearReflection_toLp_one_zero,
    inner_neg_right]
  rw [h2, h3]
  ring

/-- The mixed entries of the weak Hessian of the odd reflection. -/
private theorem ae_inner_iteratedGradient_normal_tangent_eq {a : ℝ}
    {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    {D : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    {Φ : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)} {y : E}
    (h6 : HasWeakLineDerivOn volume ⊤
      (fun x => ⟪G x, WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ -
        ⟪G (normalReflection E a x), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ)
      (fun x => ⟪D x (WithLp.toLp 2 ((1 : ℝ), (0 : E))) +
        normalLinearReflection E (D (normalReflection E a x) (WithLp.toLp 2 ((1 : ℝ), (0 : E)))),
          WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ) (WithLp.toLp 2 ((1 : ℝ), (0 : E))))
    (hcomp : HasWeakLineDerivOn volume ⊤
      (fun x => ⟪G x - normalLinearReflection E (G (normalReflection E a x)),
        WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ)
      (fun x => ⟪Φ x (WithLp.toLp 2 ((1 : ℝ), (0 : E))), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ)
      (WithLp.toLp 2 ((1 : ℝ), (0 : E)))) :
    ∀ᵐ x ∂volume, ⟪Φ x (WithLp.toLp 2 ((1 : ℝ), (0 : E))), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ =
      ⟪(D x - (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
        D (normalReflection E a x) ∘L
          (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)))
            (WithLp.toLp 2 ((1 : ℝ), (0 : E))), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ := by
  have hae := (hcomp.congr_ae (Eventually.of_forall fun x =>
    inner_sub_normalLinearReflection_tangent (G x) (G (normalReflection E a x)) y)).ae_eq h6
  rw [ae_restrict_top] at hae
  filter_upwards [hae] with x h1
  rw [h1]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, normalLinearReflection_toLp_one_zero,
    map_neg, sub_neg_eq_add]

/-- The tangential entries of the weak Hessian of the odd reflection. -/
private theorem ae_inner_iteratedGradient_tangent_eq {a : ℝ}
    {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    {D : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    {Φ : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)} {y z : E}
    (h5 : HasWeakLineDerivOn volume ⊤
      (fun x => ⟪G x, WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ -
        ⟪G (normalReflection E a x), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ)
      (fun x => ⟪D x (WithLp.toLp 2 ((0 : ℝ), y)) -
        normalLinearReflection E (D (normalReflection E a x) (WithLp.toLp 2 ((0 : ℝ), y))),
          WithLp.toLp 2 ((0 : ℝ), z)⟫_ℝ) (WithLp.toLp 2 ((0 : ℝ), z)))
    (hsymm : ∀ v c, ∀ᵐ x, ⟪D x v, c⟫_ℝ = ⟪D x c, v⟫_ℝ)
    (hcomp : HasWeakLineDerivOn volume ⊤
      (fun x => ⟪G x - normalLinearReflection E (G (normalReflection E a x)),
        WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ)
      (fun x => ⟪Φ x (WithLp.toLp 2 ((0 : ℝ), z)), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ)
      (WithLp.toLp 2 ((0 : ℝ), z))) :
    ∀ᵐ x ∂volume, ⟪Φ x (WithLp.toLp 2 ((0 : ℝ), z)), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ =
      ⟪(D x - (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
        D (normalReflection E a x) ∘L
          (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)))
            (WithLp.toLp 2 ((0 : ℝ), z)), WithLp.toLp 2 ((0 : ℝ), y)⟫_ℝ := by
  have hρ := measurePreserving_normalReflection (E := E) a
  have hae := (hcomp.congr_ae (Eventually.of_forall fun x =>
    inner_sub_normalLinearReflection_tangent (G x) (G (normalReflection E a x)) y)).ae_eq h5
  rw [ae_restrict_top] at hae
  filter_upwards [hae, hsymm (WithLp.toLp 2 ((0 : ℝ), z)) (WithLp.toLp 2 ((0 : ℝ), y)),
    hρ.quasiMeasurePreserving.ae
      (hsymm (WithLp.toLp 2 ((0 : ℝ), z)) (WithLp.toLp 2 ((0 : ℝ), y)))] with x h1 h2 h3
  rw [h1]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, normalLinearReflection_toLp_zero,
    inner_sub_left, inner_normalLinearReflection_left_eq_right]
  rw [h2, h3]

/-- **The odd reflection of second-order data.** Let `f`, `G` and `D` vanish off the half-space
`{x | a < x.fst}` and lie in `Lᵖ`, let `G` be the weak gradient of `f` on the whole space, let
`x ↦ D x c` be the weak gradient of the component `⟪G, c⟫` on the half-space for every `c`, and
let `D` be symmetric. Then the odd reflection `x ↦ f x - f (ρ x)` is the value of a function in
`W^{2,p}(ℝ × E)` whose weak Hessian is `x ↦ D x - R ∘ D (ρ x) ∘ R`. -/
private theorem exists_wkp_two_sub_comp_normalReflection {a : ℝ}
    {f : WithLp 2 (ℝ × E) → ℝ} {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    {D : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hf : MemLp f p volume) (hG : MemLp G p volume) (hD : ∀ c, MemLp (fun x => D x c) p volume)
    (hG0 : ∀ x ∉ normalHalfSpace (E := E) a, G x = 0)
    (hD0 : ∀ x ∉ normalHalfSpace (E := E) a, D x = 0)
    (hfG : HasWeakFDerivOn volume ⊤ f fun x => innerSL ℝ (G x))
    (hGD : ∀ c, HasWeakFDerivOn volume (normalHalfSpace a) (fun x => ⟪G x, c⟫_ℝ)
      fun x => innerSL ℝ (D x c))
    (hsymm : ∀ v c, ∀ᵐ x, ⟪D x v, c⟫_ℝ = ⟪D x c, v⟫_ℝ) :
    ∃ W : Wkp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p 2,
      Wkp.value 2 W =ᵐ[volume] (fun x => f x - f (normalReflection E a x)) ∧
      Wkp.iteratedGradient 1 W =ᵐ[volume] fun x =>
        D x - (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
          D (normalReflection E a x) ∘L
            (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) := by
  -- Write `ν = (1, 0)` and `τ y = (0, y)`. The odd reflection `f - f ∘ ρ` has weak gradient
  -- `G - R (G ∘ ρ)` (`h2`), whose components are first-order Sobolev functions (`h4`, `h5`, `h6`),
  -- so it is the value of an element `W` of `W^{2,p}`. The entries of its weak Hessian are
  -- identified with those of `D - R ∘ D ∘ ρ ∘ R` by uniqueness of weak derivatives.
  have h2 := hasWeakFDerivOn_sub_comp_normalReflection_innerSL (a := a) hfG
  have h4 := hasWeakFDerivOn_inner_normal_add_comp_normalReflection hG hD hG0 hD0 hGD
  have h5 := hasWeakLineDerivOn_inner_tangent_sub_comp_normalReflection hG hD hG0 hD0 hGD
  have h6 := hasWeakLineDerivOn_inner_tangent_sub_comp_normalReflection_normal h2 h4
  obtain ⟨N, hN⟩ := exists_wkp_one_value_ae_eq_inner_normal_add_comp_normalReflection hG hD h4
  choose T hT using
    exists_wkp_one_value_ae_eq_inner_tangent_sub_comp_normalReflection hG hD h5 h6
  obtain ⟨W, hW, hg⟩ :=
    exists_wkp_two_value_ae_eq_sub_comp_normalReflection hf h2 N T hN hT
  refine ⟨W, hW, ?_⟩
  have hcomp := hasWeakLineDerivOn_inner_iteratedGradient_one W hg
  exact ae_clm_eq_of_forall_inner_normal_tangent
    (ae_inner_iteratedGradient_normal_eq h4 hsymm fun v => hcomp _ v)
    (fun y => ae_inner_iteratedGradient_normal_tangent_eq (h6 y) (hcomp _ _))
    fun y z => ae_inner_iteratedGradient_tangent_eq (h5 y z) hsymm (hcomp _ _)

/-- **Odd reflection of a second-order Sobolev function with zero boundary values.** Let
`u ∈ W^{2,p}(H)` on the half-space `H = {x | a < x.fst}` of `ℝ × E` have first-order part in
`W^{1,p}_0(H)`. Then the odd reflection of `u` across the boundary hyperplane, equal to `u` on `H`
and to `-u ∘ ρ` on the other side, lies in `W^{2,p}(ℝ × E)`, and its weak Hessian is `D²u` on `H`
and `-R ∘ D²u (ρ x) ∘ R` on the other side. Here `ρ (t, y) = (2a - t, y)` is the reflection in
`{a} × E` and `R (s, z) = (-s, z)` its linear part. -/
theorem Wkp.exists_value_ae_eq_sub_comp_normalReflection {a : ℝ}
    (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2)
    (hu : Wkp.firstOrder 1 u ∈ w1p0Submodule volume (normalHalfSpace a) p) :
    ∃ w : Wkp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p 2,
      Wkp.value 2 w =ᵐ[volume] (fun x =>
        (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator (Wkp.value 2 u) x -
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator (Wkp.value 2 u)
            (normalReflection E a x)) ∧
      Wkp.iteratedGradient 1 w =ᵐ[volume] fun x =>
        (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator
            (Wkp.iteratedGradient 1 u) x -
          (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
            (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator
              (Wkp.iteratedGradient 1 u) (normalReflection E a x) ∘L
            (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) := by
  set S := (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
  have hS : MeasurableSet S := (normalHalfSpace (E := E) a).isOpen.measurableSet
  set g := Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)
  set D := Wkp.iteratedGradient 1 u
  have hDl := (memLp_indicator_iff_restrict hS.nullMeasurableSet).2 (Lp.memLp D)
  -- the first-order part of `u`, extended by zero, is a Sobolev function on the whole space
  have hfG : HasWeakFDerivOn volume ⊤ (S.indicator (Wkp.value 2 u))
      fun x => innerSL ℝ (S.indicator g x) := by
    set w := (W1p0.extendByZeroL le_top ⟨Wkp.firstOrder 1 u, hu⟩ :
      W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p)
    have hval : W1p.value (Wkp.firstOrder 1 u) = Wkp.value 2 u := by
      rw [Wkp.value_succ, Wkp.value_one, Wkp.firstOrder_succ, Wkp.firstOrder_zero]
    have hgrad : W1p.gradient (Wkp.firstOrder 1 u) = g :=
      (congrArg W1p.gradient ((Wkp.firstOrder_succ 0 u).trans (Wkp.firstOrder_zero _))).trans
        (Wkp.iteratedGradient_zero (Wkp.lowerOrder 1 u)).symm
    have hv := coeFn_extendByZeroLpₗᵢ ℝ hS (SetLike.coe_subset_coe.mpr le_top)
      (W1p.value (Wkp.firstOrder 1 u))
    have hg := coeFn_extendByZeroLpₗᵢ ℝ hS (SetLike.coe_subset_coe.mpr le_top)
      (W1p.gradient (Wkp.firstOrder 1 u))
    refine ((W1p.hasWeakFDerivOn w).congr_ae ?_).congr_ae_deriv ?_
    · rw [W1p0.value_extendByZeroL]
      exact hv.trans (EventuallyEq.of_eq (by rw [hval]))
    · rw [W1p0.gradient_extendByZeroL]
      filter_upwards [hg.trans (EventuallyEq.of_eq (by rw [hgrad]))] with x hx
      rw [hx]
  refine exists_wkp_two_sub_comp_normalReflection
    ((memLp_indicator_iff_restrict hS.nullMeasurableSet).2 (Lp.memLp _))
    ((memLp_indicator_iff_restrict hS.nullMeasurableSet).2 (Lp.memLp g)) (fun c => ?_)
    (fun x hx => indicator_of_notMem hx _) (fun x hx => indicator_of_notMem hx _) hfG
    (fun c => ?_) (fun v c => ?_)
  · -- the entries of the extended Hessian are in `Lᵖ`
    exact (ContinuousLinearMap.apply ℝ (WithLp 2 (ℝ × E)) c).comp_memLp' hDl
  · -- `x ↦ D²u x c` is the weak gradient of `⟪∇u, c⟫` on the half-space, by symmetry of `D²u`
    rw [hasWeakFDerivOn_iff]
    intro d
    refine ((((Wkp.hasWeakFDerivOn_iteratedGradient 0 u).clm_comp
      (innerSL ℝ c)).hasWeakLineDerivOn d).congr_ae ?_).congr_ae_deriv ?_
    · filter_upwards [ae_restrict_mem hS] with x hx
      rw [indicator_of_mem hx, innerSL_apply_apply]
      exact real_inner_comm _ _
    · filter_upwards [ae_restrict_mem hS, Wkp.inner_iteratedGradient_one_apply_ae_eq u d c]
        with x hx hsym
      simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, indicator_of_mem hx]
      rw [real_inner_comm, hsym]
  · -- the extended Hessian is symmetric
    filter_upwards [(ae_restrict_iff' hS).1 (Wkp.inner_iteratedGradient_one_apply_ae_eq u v c)]
      with x hx
    by_cases hxS : x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
    · simp only [indicator_of_mem hxS]
      exact hx hxS
    · simp only [indicator_of_notMem hxS, zero_apply, inner_zero_left]

end Construction

end TauCeti
