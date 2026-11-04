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
  -- Write `ν = (1, 0)` and `τ y = (0, y)`. We first compute the weak derivatives of the
  -- components of the gradient `G - R (G ∘ ρ)` of the odd reflection, in every direction; they
  -- show that `f - f ∘ ρ` is the value of an element `W` of `W^{2,p}`. Then the entries of the
  -- weak Hessian of `W` along a basis adapted to the hyperplane are identified by uniqueness of
  -- weak derivatives.
  set ρ := normalReflection E a
  set R := normalLinearReflection E
  set ν : WithLp 2 (ℝ × E) := WithLp.toLp 2 ((1 : ℝ), (0 : E))
  set τ : E → WithLp 2 (ℝ × E) := fun y => WithLp.toLp 2 ((0 : ℝ), y)
  have hρ := measurePreserving_normalReflection (E := E) a
  have hRν : R ν = -ν := by simp [R, ν, ← WithLp.toLp_neg]
  have hRτ (y : E) : R (τ y) = τ y := by simp [R, τ]
  have hτ (y : E) : (τ y).fst = 0 := rfl
  have hsplit (v : WithLp 2 (ℝ × E)) : v.fst • ν + τ v.snd = v := by
    cases v; simp [ν, τ, ← WithLp.toLp_smul, ← WithLp.toLp_add]
  -- `Lᵖ` bounds and local integrability of the pieces
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hGc (c : WithLp 2 (ℝ × E)) : MemLp (fun x => ⟪G x, c⟫_ℝ) p volume := hG.inner_const c
  have hρGc (c : WithLp 2 (ℝ × E)) : MemLp (fun x => ⟪G (ρ x), c⟫_ℝ) p volume :=
    (hGc c).comp_measurePreserving hρ
  have hρD (c : WithLp 2 (ℝ × E)) : MemLp (fun x => R (D (ρ x) c)) p volume :=
    (R : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)).comp_memLp' ((hD c).comp_measurePreserving hρ)
  have hplus (c d : WithLp 2 (ℝ × E)) :
      MemLp (fun x => ⟪D x c + R (D (ρ x) c), d⟫_ℝ) p volume :=
    ((hD c).add (hρD c)).inner_const d
  have hminus (c d : WithLp 2 (ℝ × E)) :
      MemLp (fun x => ⟪D x c - R (D (ρ x) c), d⟫_ℝ) p volume :=
    ((hD c).sub (hρD c)).inner_const d
  have hGc0 (c : WithLp 2 (ℝ × E)) (x : WithLp 2 (ℝ × E)) (hx : x ∉ normalHalfSpace (E := E) a) :
      ⟪G x, c⟫_ℝ = 0 := by
    simp [hG0 x hx]
  have hDc0 (c : WithLp 2 (ℝ × E)) (x : WithLp 2 (ℝ × E)) (hx : x ∉ normalHalfSpace (E := E) a) :
      D x c = 0 := by
    simp [hD0 x hx]
  -- the first derivatives of the odd reflection
  have h2 : HasWeakFDerivOn volume ⊤ (fun x => f x - f (ρ x))
      fun x => innerSL ℝ (G x - R (G (ρ x))) :=
    (hfG.sub hfG.comp_normalReflection).congr_ae_deriv
      (Eventually.of_forall fun x => by simp only [Pi.sub_apply, map_sub, ρ, R])
  have hν (x : WithLp 2 (ℝ × E)) :
      ⟪G x - R (G (ρ x)), ν⟫_ℝ = ⟪G x, ν⟫_ℝ + ⟪G (ρ x), ν⟫_ℝ := by
    rw [inner_sub_left, inner_normalLinearReflection_left_eq_right, hRν, inner_neg_right,
      sub_neg_eq_add]
  have hτν (y : E) (x : WithLp 2 (ℝ × E)) :
      ⟪G x - R (G (ρ x)), τ y⟫_ℝ = ⟪G x, τ y⟫_ℝ - ⟪G (ρ x), τ y⟫_ℝ := by
    rw [inner_sub_left, inner_normalLinearReflection_left_eq_right, hRτ]
  -- the normal component `∂_ν (f - f ∘ ρ)` is the even reflection of `⟪G, ν⟫`
  have h4 := (hGD ν).add_comp_normalReflection ((hGc ν).locallyIntegrable hp)
    ((hD ν).locallyIntegrable hp) (hGc0 ν) (hDc0 ν)
  -- the tangential components are odd reflections, with tangential derivatives ...
  have h5 (y z : E) := (hGD (τ y)).hasWeakLineDerivOn_sub_comp_normalReflection
    ((hGc (τ y)).locallyIntegrable hp) ((hD (τ y)).locallyIntegrable hp) (hGc0 (τ y))
    (hDc0 (τ y)) (d := τ z) (hτ z)
  -- ... and normal derivative obtained by commuting the two weak derivatives
  have h6 (y : E) : HasWeakLineDerivOn volume ⊤ (fun x => ⟪G x, τ y⟫_ℝ - ⟪G (ρ x), τ y⟫_ℝ)
      (fun x => ⟪D x ν + R (D (ρ x) ν), τ y⟫_ℝ) ν := by
    have h₁ := (h2.hasWeakLineDerivOn ν).congr_ae_deriv
      (Eventually.of_forall fun x => (innerSL_apply_apply ℝ _ _).trans (hν x))
    have h₂ := (h2.hasWeakLineDerivOn (τ y)).congr_ae_deriv
      (Eventually.of_forall fun x => (innerSL_apply_apply ℝ _ _).trans (hτν y x))
    simpa only [innerSL_apply_apply] using h₁.comm (h4.hasWeakLineDerivOn (τ y)) h₂
  -- the components of the gradient are first-order Sobolev functions
  obtain ⟨N, hN⟩ : ∃ N : Wkp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p 1,
      Wkp.value 1 N =ᵐ[volume] fun x => ⟪G x, ν⟫_ℝ + ⟪G (ρ x), ν⟫_ℝ := by
    have h := Wkp.exists_value_one_ae_eq_of_forall_hasWeakLineDerivOn
      (w := fun x => ⟪G x, ν⟫_ℝ + ⟪G (ρ x), ν⟫_ℝ) (((hGc ν).add (hρGc ν)).restrict _)
      (fun v x => ⟪D x ν + R (D (ρ x) ν), v⟫_ℝ)
      (fun v => (hplus ν v).restrict _) fun v => by
        simpa only [innerSL_apply_apply] using h4.hasWeakLineDerivOn v
    rw [ae_restrict_top] at h
    exact h
  have hT (y : E) : ∃ T : Wkp (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p 1,
      Wkp.value 1 T =ᵐ[volume] fun x => ⟪G x, τ y⟫_ℝ - ⟪G (ρ x), τ y⟫_ℝ := by
    have h := Wkp.exists_value_one_ae_eq_of_forall_hasWeakLineDerivOn
      (w := fun x => ⟪G x, τ y⟫_ℝ - ⟪G (ρ x), τ y⟫_ℝ)
      (((hGc (τ y)).sub (hρGc (τ y))).restrict _)
      (fun v x => v.fst * ⟪D x ν + R (D (ρ x) ν), τ y⟫_ℝ +
        ⟪D x (τ y) - R (D (ρ x) (τ y)), τ v.snd⟫_ℝ)
      (fun v => (((hplus ν (τ y)).const_mul v.fst).add (hminus (τ y) (τ v.snd))).restrict _)
      fun v => by
        have h := ((h6 y).smul_direction v.fst).add_direction (h5 y v.snd)
        rw [hsplit v] at h
        exact h
    rw [ae_restrict_top] at h
    exact h
  choose T hT using hT
  -- the odd reflection is a second-order Sobolev function
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
  -- the weak gradient of `W` is `G - R (G ∘ ρ)`
  have hg : ∀ᵐ x ∂volume,
      Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 W) x = G x - R (G (ρ x)) := by
    have hval : Wkp.value 1 (Wkp.lowerOrder 1 W) =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict
        ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E)))]
        fun x => f x - f (ρ x) := by
      rw [ae_restrict_top, ← Wkp.value_succ]
      exact hW
    have h := ((Wkp.hasWeakFDerivOn_value (Wkp.lowerOrder 1 W)).congr_ae hval).ae_eq h2
    rw [ae_restrict_top] at h
    filter_upwards [h] with x hx
    exact ext_inner_right ℝ fun v => by
      simpa only [innerSL_apply_apply] using DFunLike.congr_fun hx v
  -- each entry of the weak Hessian of `W` is a weak derivative of a component of `G - R (G ∘ ρ)`
  have hcomp (c v : WithLp 2 (ℝ × E)) : HasWeakLineDerivOn volume ⊤
      (fun x => ⟪G x - R (G (ρ x)), c⟫_ℝ) (fun x => ⟪Wkp.iteratedGradient 1 W x v, c⟫_ℝ) v := by
    have h : HasWeakLineDerivOn volume ⊤
        (fun x => ⟪Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 W) x, c⟫_ℝ)
        (fun x => ⟪Wkp.iteratedGradient 1 W x v, c⟫_ℝ) v := by
      simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm c] using
        ((Wkp.hasWeakFDerivOn_iteratedGradient 0 W).clm_comp (innerSL ℝ c)).hasWeakLineDerivOn v
    refine h.congr_ae ?_
    rw [ae_restrict_top]
    filter_upwards [hg] with x hx
    rw [hx]
  -- compare the entries along an orthonormal basis adapted to the hyperplane
  set b := (OrthonormalBasis.singleton Unit ℝ).prod (stdOrthonormalBasis ℝ E)
  have hb_inl : b (Sum.inl ()) = ν := by simp [b, ν]
  have hb_inr (j : Fin (Module.finrank ℝ E)) : b (Sum.inr j) = τ (stdOrthonormalBasis ℝ E j) := by
    simp [b, τ]
  have hentry (i j : Unit ⊕ Fin (Module.finrank ℝ E)) : ∀ᵐ x ∂volume,
      ⟪Wkp.iteratedGradient 1 W x (b i), b j⟫_ℝ =
        ⟪(D x - (R : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L D (ρ x) ∘L
          (R : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))) (b i), b j⟫_ℝ := by
    rcases j with ⟨⟩ | j
    · -- the normal component is the even reflection of `⟪G, ν⟫`
      have hae := ((hcomp ν (b i)).congr_ae (Eventually.of_forall hν)).ae_eq
        (h4.hasWeakLineDerivOn (b i))
      rw [ae_restrict_top] at hae
      filter_upwards [hae, hsymm (b i) ν, hρ.quasiMeasurePreserving.ae (hsymm (R (b i)) ν)]
        with x h1 h2 h3
      rw [hb_inl, h1]
      simp only [ρ, R] at hRν h3 ⊢
      simp only [innerSL_apply_apply, sub_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv, inner_add_left, inner_sub_left,
        inner_normalLinearReflection_left_eq_right, hRν, inner_neg_right]
      rw [h2, h3]
      ring
    · rcases i with ⟨⟩ | i
      · -- a mixed entry: the normal derivative of a tangential component
        have hae := ((hcomp (τ (stdOrthonormalBasis ℝ E j)) ν).congr_ae
          (Eventually.of_forall (hτν _))).ae_eq (h6 (stdOrthonormalBasis ℝ E j))
        rw [ae_restrict_top] at hae
        filter_upwards [hae] with x h1
        rw [hb_inl, hb_inr, h1]
        simp only [ρ, R] at hRν ⊢
        simp only [sub_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, hRν,
          map_neg, sub_neg_eq_add]
      · -- a tangential entry: the odd reflection of `⟪D τ, τ'⟫`
        set y := stdOrthonormalBasis ℝ E j
        set z := stdOrthonormalBasis ℝ E i
        have hae := ((hcomp (τ y) (τ z)).congr_ae
          (Eventually.of_forall (hτν y))).ae_eq (h5 y z)
        rw [ae_restrict_top] at hae
        filter_upwards [hae, hsymm (τ z) (τ y), hρ.quasiMeasurePreserving.ae (hsymm (τ z) (τ y))]
          with x h1 h2 h3
        rw [hb_inr, hb_inr, h1]
        simp only [ρ, R] at hRτ h3 ⊢
        simp only [sub_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, hRτ,
          inner_sub_left, inner_normalLinearReflection_left_eq_right]
        rw [h2, h3]
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hentry i j] with x hx
  exact ContinuousLinearMap.coe_injective (b.toBasis.ext fun i =>
    InnerProductSpace.ext_inner_right_basis b.toBasis fun j => by simpa using hx i j)

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
