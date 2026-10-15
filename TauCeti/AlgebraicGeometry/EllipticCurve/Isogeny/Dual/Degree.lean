/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Add
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Degree
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
-- Proof-only: `monicity!` and `field_simp`.
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp

/-!
# The degree is a quadratic form

For morphisms `f, g : W₁ → W₂` of elliptic curves over a field, the symmetric cross-composite of
duals is the polarisation of the degree:

    f̂ ∘ g + ĝ ∘ f = [deg (f + g) − deg f − deg g].

Indeed, expanding `(f + g)^ ∘ (f + g) = [deg (f + g)]` by additivity of the dual
(`TauCeti.Isogeny.Hom.dual_add`) and biadditivity of composition leaves
`[deg f] + f̂ ∘ g + ĝ ∘ f + [deg g]`. The cross-composite is additive in each variable, and
`n ↦ [n]` is injective, so the polarisation is bilinear. Together with `deg (n f) = n² deg f`
(`TauCeti.Isogeny.Hom.degree_zsmul`), this makes the degree, extended by `deg 0 = 0`, a quadratic
form on `Hom W₁ W₂`, positive definite since only the zero map has degree zero
(Silverman III.6.3). No separability or closure hypothesis is made.

## Main definitions

* `TauCeti.Isogeny.Hom.degreeForm`: the degree as a `ℤ`-valued quadratic form on `Hom W₁ W₂`.

## Main results

* `TauCeti.Isogeny.Hom.dual_comp_add_dual_comp`: `f̂ ∘ g + ĝ ∘ f` is multiplication by the degree
  polarisation.
* `TauCeti.Isogeny.Hom.polar_degree_add_left` and `TauCeti.Isogeny.Hom.polar_degree_add_right`:
  the degree polarisation is additive in each variable.
* `TauCeti.Isogeny.Hom.degreeForm_posDef`: the degree form is positive definite.
* `TauCeti.Isogeny.Hom.dual_eq_polar_smul_one_sub`: an endomorphism `f` satisfies
  `f̂ = t - f` for the integer `t = deg (f + 1) - deg f - 1`, its trace.
* `TauCeti.Isogeny.Hom.mul_self_eq_polar_smul_sub_degree`: an endomorphism `f` is a root of
  `X² - t X + deg f`.
* `TauCeti.Isogeny.Hom.mem_range_of_zsmul_mem_range`: the image of an integrally closed ring
  embedded in the endomorphism ring is saturated.
* `TauCeti.Isogeny.Hom.dual_two_nsmul_sub_polar_smul_one`: `2f - t` is anti-self-dual.
* `TauCeti.Isogeny.Hom.mul_self_eq_neg_degree_of_dual_eq_neg`: an anti-self-dual endomorphism
  squares to minus its degree.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.2–3.
-/

public section

namespace TauCeti.Isogeny.Hom

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The symmetric dual composite is the polarisation of the degree**:
`f̂ ∘ g + ĝ ∘ f = [deg (f + g) − deg f − deg g]` (Silverman III.6.3). -/
theorem dual_comp_add_dual_comp (f g : Hom W₁ W₂) :
    f.dual.comp g + g.dual.comp f =
      QuadraticMap.polar (fun h : Hom W₁ W₂ ↦ (h.degree : ℤ)) f g • id W₁ := by
  have h := (f + g).dual_comp_self
  rw [dual_add, add_comp, comp_add, comp_add, dual_comp_self, dual_comp_self] at h
  rw [QuadraticMap.polar, sub_smul, sub_smul, natCast_zsmul, natCast_zsmul, natCast_zsmul, ← h]
  abel

/-- **The degree polarisation is additive in the left variable.** -/
theorem polar_degree_add_left (f f' g : Hom W₁ W₂) :
    QuadraticMap.polar (fun h : Hom W₁ W₂ ↦ (h.degree : ℤ)) (f + f') g =
      QuadraticMap.polar (fun h : Hom W₁ W₂ ↦ (h.degree : ℤ)) f g +
        QuadraticMap.polar (fun h : Hom W₁ W₂ ↦ (h.degree : ℤ)) f' g := by
  refine zsmul_id_injective (W₁ := W₁) ?_
  simp only [add_smul, ← dual_comp_add_dual_comp, dual_add, add_comp, comp_add]
  abel

/-- **The degree polarisation is additive in the right variable.** -/
theorem polar_degree_add_right (f g g' : Hom W₁ W₂) :
    QuadraticMap.polar (fun h : Hom W₁ W₂ ↦ (h.degree : ℤ)) f (g + g') =
      QuadraticMap.polar (fun h : Hom W₁ W₂ ↦ (h.degree : ℤ)) f g +
        QuadraticMap.polar (fun h : Hom W₁ W₂ ↦ (h.degree : ℤ)) f g' := by
  simp only [QuadraticMap.polar_comm _ f, polar_degree_add_left]

variable (W₁ W₂) in
/-- **The degree is a quadratic form** on the morphisms `W₁ → W₂` (Silverman III.6.3), with the
zero map of degree zero. -/
noncomputable def degreeForm : QuadraticMap ℤ (Hom W₁ W₂) ℤ :=
  QuadraticMap.ofPolar (fun f ↦ (f.degree : ℤ))
    (fun n f ↦ by simp [sq])
    polar_degree_add_left
    (fun n f g ↦ by
      refine zsmul_id_injective (W₁ := W₁) ?_
      simp only [← dual_comp_add_dual_comp, smul_eq_mul, mul_smul, dual_zsmul, zsmul_comp,
        comp_zsmul, smul_add])

@[simp]
theorem degreeForm_apply (f : Hom W₁ W₂) : degreeForm W₁ W₂ f = f.degree :=
  (rfl)

/-- **The degree form is positive definite**: every nonzero morphism has positive degree. -/
theorem degreeForm_posDef : (degreeForm W₁ W₂).PosDef := fun f hf ↦ by
  simpa [Nat.pos_iff_ne_zero] using hf

section Endomorphism

variable {W : WeierstrassCurve.Affine F} [W.IsElliptic]

/-- **The dual of an endomorphism is its trace minus itself**: `f̂ = t - f`, where the trace
`t = deg (f + 1) - deg f - 1` is the degree polarisation of `f` and `1` (Silverman III.6.2). -/
theorem dual_eq_polar_smul_one_sub (f : Hom W W) :
    f.dual = QuadraticMap.polar (fun h : Hom W W ↦ (h.degree : ℤ)) f 1 • 1 - f := by
  have h := dual_comp_add_dual_comp f (id W)
  rw [comp_id, dual_id, id_comp, ← one_def] at h
  rw [← h, add_sub_cancel_right]

/-- **An endomorphism is a root of its characteristic polynomial** `X² - t X + deg f`, where `t` is
its trace: `f² = t f - deg f`, which is `f̂ ∘ f = [deg f]` with `f̂ = t - f`
(Silverman III.6.2). -/
theorem mul_self_eq_polar_smul_sub_degree (f : Hom W W) :
    f * f = QuadraticMap.polar (fun h : Hom W W ↦ (h.degree : ℤ)) f 1 • f - (f.degree : ℤ) • 1 := by
  have h := f.dual_comp_self
  rw [dual_eq_polar_smul_one_sub, ← mul_def, ← one_def, ← natCast_zsmul, sub_mul, smul_mul_assoc,
    one_mul] at h
  rw [← h, sub_sub_cancel]

/-- **The image of an integrally closed ring in the endomorphism ring is saturated**: if `ι` embeds
an integrally closed ring `R` into `End(W)`, and a nonzero integer multiple `N f` of an
endomorphism `f` lies in the image of `ι`, then so does `f`. -/
theorem mem_range_of_zsmul_mem_range {R : Type*} [CommRing R] [IsIntegrallyClosed R]
    {ι : R →+* Hom W W} (hι : Function.Injective ι) {f : Hom W W} {N : ℤ} (hN : N ≠ 0)
    (hf : N • f ∈ Set.range ι) : f ∈ Set.range ι := by
  obtain ⟨z, hz⟩ := hf
  have := hι.isDomain ι
  set t := QuadraticMap.polar (fun h : Hom W W ↦ (h.degree : ℤ)) f 1
  set d : ℤ := (f.degree : ℤ)
  -- `z = N f` is a root of `X² - N t X + N² d`, as `f` is a root of `X² - t X + d`
  have hz2 : z * z = (N * t : ℤ) • z - (N ^ 2 * d : ℤ) • 1 := by
    refine hι ?_
    rw [_root_.map_mul, _root_.map_sub, _root_.map_zsmul, _root_.map_zsmul, _root_.map_one, hz,
      smul_mul_smul_comm, mul_self_eq_polar_smul_sub_degree]
    module
  -- so `z / N` is a root of `X² - t X + d` in the fraction field, hence lies in `R`
  have hNR : (N : R) ≠ 0 := fun h ↦ hN <| by
    simpa using congrArg ι h
  have hNK : (N : FractionRing R) ≠ 0 := by
    rw [← _root_.map_intCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hNR
  have hint : IsIntegral R (algebraMap R (FractionRing R) z / N) := by
    refine ⟨.X ^ 2 - .C (t : R) * .X + .C (d : R), by monicity!, ?_⟩
    have hzK := congrArg (algebraMap R (FractionRing R)) hz2
    simp only [_root_.map_mul, _root_.map_sub, zsmul_eq_mul, mul_one, _root_.map_intCast,
      _root_.map_pow, Int.cast_mul, Int.cast_pow] at hzK
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Polynomial.eval₂_X]
    simp only [_root_.map_intCast]
    field_simp
    linear_combination hzK
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hzy : z = N * y := IsFractionRing.injective R (FractionRing R) <| by
    rw [_root_.map_mul, hy, _root_.map_intCast, mul_div_cancel₀ _ hNK]
  refine ⟨y, smul_right_injective _ hN (?_ : N • ι y = N • f)⟩
  rw [← hz, hzy, _root_.map_mul, _root_.map_intCast, ← zsmul_eq_mul]

/-- **Twice an endomorphism minus its trace is anti-self-dual**: `(2f - t)^ = -(2f - t)`. -/
theorem dual_two_nsmul_sub_polar_smul_one (f : Hom W W) :
    (2 • f - QuadraticMap.polar (fun h : Hom W W ↦ (h.degree : ℤ)) f 1 • 1).dual =
      -(2 • f - QuadraticMap.polar (fun h : Hom W W ↦ (h.degree : ℤ)) f 1 • 1) := by
  rw [dual_sub, dual_nsmul, dual_zsmul, dual_eq_polar_smul_one_sub, one_def, dual_id]
  abel

/-- **An anti-self-dual endomorphism squares to minus its degree**: if `x̂ = -x`, then
`x² = -x x̂ = -deg x`. -/
theorem mul_self_eq_neg_degree_of_dual_eq_neg {x : Hom W W} (hx : x.dual = -x) :
    x * x = -((x.degree : ℤ) • 1) := by
  have h := x.comp_dual_self
  rw [hx, comp_neg, ← mul_def, ← one_def, ← natCast_zsmul] at h
  rw [← h, neg_neg]

end Endomorphism

end TauCeti.Isogeny.Hom

end
