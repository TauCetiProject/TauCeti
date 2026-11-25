/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Kaehler.FreeQuotient
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Div

/-!
# Checks: the local rings of the node and the cusp at the origin

For a field `k` and `f ∈ k[x, y]` vanishing at the origin, let `O_f` be the local ring at the
origin of `k[x, y] / (f)`. Then `Ω[O_f⁄k]` admits no surjection onto `O_f ^ d` with `d ≠ 0` when

* `f = x y` is the node, in every characteristic (`node_not_surjective`), and
* `f = y ^ 2 - x ^ 3` is the cusp and `2 ≠ 0`, `3 ≠ 0` in `k`, for instance over `ℚ`
  (`cusp_not_surjective`).

These are the ring-level halves of the node example and of the cusp Check of NashBlowups §0.7: by
the forward stalk criterion `HasLocallyFreeQuotientOfDifferentials.exists_surjective_stalk`,
applied at the origin, `HasLocallyFreeQuotientOfDifferentials` of rank one fails for the node and
for the cusp over `ℚ` once the stalk there is identified with `O_f` as a `k`-algebra. Over `𝔽_2`
the cusp has the free quotient `dx ↦ 0`, `dy ↦ 1`, so the characteristic hypothesis on the cusp
cannot be dropped.

The non-divisibility hypotheses of `TauCeti.not_surjective_kaehlerDifferential_of_mul_eq_zero`
and `TauCeti.not_surjective_kaehlerDifferential_of_sq_eq_pow_three` are checked by mapping `O_f`
to rings where the images of `x`, `y` are explicit: `k⟦t⟧` with `(x, y) ↦ (t, 0)`, `(0, t)` or
`(t ^ 2, t ^ 3)`, and `k[t] / (t ^ 3)` with `(x, y) ↦ (t, 0)`.
-/

public section

noncomputable section

open MvPolynomial KaehlerDifferential

namespace TauCeti.NodeCuspDifferentialsExample

universe u

variable {k : Type u} [Field k]

section Origin

variable (k) in
/-- The coordinate ring `k[x, y] / (f)` of the plane curve `f = 0`. -/
abbrev Curve (f : MvPolynomial (Fin 2) k) : Type u := MvPolynomial (Fin 2) k ⧸ Ideal.span {f}

/-- A shortcut instance: without it, instance search for the module structure on the Kähler
differentials of a localization of `Curve k f` fails to find the ring structure of the quotient. -/
instance instCommRingCurve (f : MvPolynomial (Fin 2) k) : CommRing (Curve k f) :=
  Ideal.Quotient.commRing _

variable (f : MvPolynomial (Fin 2) k)

/-- Evaluation at the origin on `k[x, y] / (f)`, for `f` vanishing at the origin. -/
def evalOrigin (hf : eval 0 f = 0) : Curve k f →+* k :=
  Ideal.Quotient.lift _ (eval 0) fun a ha ↦ by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hf, mul_zero]

@[simp]
lemma evalOrigin_mk (hf : eval 0 f = 0) (a : MvPolynomial (Fin 2) k) :
    evalOrigin f hf (Ideal.Quotient.mk _ a) = eval 0 a :=
  Ideal.Quotient.lift_mk _ _ _

/-- The maximal ideal of `k[x, y] / (f)` at the origin. -/
def origin (hf : eval 0 f = 0) : Ideal (Curve k f) := RingHom.ker (evalOrigin f hf)

instance origin.isMaximal (hf : eval 0 f = 0) : (origin f hf).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨Ideal.Quotient.mk _ (C c), by simp⟩

/-- The local ring at the origin of the plane curve `f = 0`. -/
abbrev LocalRingAt (hf : eval 0 f = 0) : Type u := Localization.AtPrime (origin f hf)

/-- The coordinate `x` in the local ring at the origin. -/
abbrev xc (hf : eval 0 f = 0) : LocalRingAt f hf :=
  algebraMap (Curve k f) (LocalRingAt f hf) (Ideal.Quotient.mk (Ideal.span {f}) (X 0))

/-- The coordinate `y` in the local ring at the origin. -/
abbrev yc (hf : eval 0 f = 0) : LocalRingAt f hf :=
  algebraMap (Curve k f) (LocalRingAt f hf) (Ideal.Quotient.mk (Ideal.span {f}) (X 1))

variable (hf : eval 0 f = 0)

/-- The differentials of the coordinates span the Kähler differentials of the local ring. -/
theorem span_D_eq_top :
    Submodule.span (LocalRingAt f hf) {D k _ (xc f hf), D k _ (yc f hf)} = ⊤ := by
  have hs : Algebra.adjoin k (Set.range fun i ↦ Ideal.Quotient.mk (Ideal.span {f}) (X i)) = ⊤ := by
    have := congrArg (Subalgebra.map (Ideal.Quotient.mkₐ k (Ideal.span {f}))) (adjoin_range_X)
    rw [AlgHom.map_adjoin, Algebra.map_top,
      (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective k _), ← Set.range_comp] at this
    exact this
  have h :=
    span_D_image_eq_top_of_isLocalization (R := LocalRingAt f hf) (origin f hf).primeCompl hs
  convert h using 2
  ext ω
  simp [Fin.exists_fin_two, eq_comm]

/-- To see that `u ∉ (v)` in the local ring at the origin, it suffices to find a ring map
`ψ : k[x, y] / (f) → B` sending the elements off the origin to units with `ψ u ∉ (ψ v)`. -/
theorem notMem_span_of_ringHom {B : Type*} [CommRing B] (ψ : Curve k f →+* B)
    (hψ : ∀ a, evalOrigin f hf a ≠ 0 → IsUnit (ψ a)) {u v : Curve k f}
    (h : ψ u ∉ Ideal.span {ψ v}) :
    algebraMap _ (LocalRingAt f hf) u ∉ Ideal.span {algebraMap _ (LocalRingAt f hf) v} := by
  have hM : ∀ s : (origin f hf).primeCompl, IsUnit (ψ s) := fun s ↦ hψ s s.property
  let L := IsLocalization.lift (M := (origin f hf).primeCompl) (S := LocalRingAt f hf) hM
  intro hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  refine h (Ideal.mem_span_singleton'.mpr ⟨L c, ?_⟩)
  rw [← IsLocalization.lift_eq (M := (origin f hf).primeCompl) (S := LocalRingAt f hf) hM u,
    ← hc, map_mul, IsLocalization.lift_eq]

/-- The map `k[x, y] / (f) → k⟦t⟧` sending `x`, `y` to power series `p 0`, `p 1` with vanishing
constant terms and `f(p) = 0` sends the elements off the origin to units. -/
theorem isUnit_powerSeries {p : Fin 2 → PowerSeries k}
    (hp : ∀ i, PowerSeries.constantCoeff (p i) = 0) (hfp : aeval p f = 0) (a : Curve k f)
    (ha : evalOrigin f hf a ≠ 0) :
    IsUnit (Ideal.Quotient.lift _ (aeval p).toRingHom (fun b hb ↦ by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      change aeval p (c * f) = 0
      rw [map_mul, hfp, mul_zero]) a) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [PowerSeries.isUnit_iff_constantCoeff, Ideal.Quotient.lift_mk]
  have : (PowerSeries.constantCoeff).comp (aeval p).toRingHom = eval 0 :=
    MvPolynomial.ringHom_ext (fun c ↦ by simp) (fun i ↦ by simp [hp])
  rw [← RingHom.comp_apply, this]
  rw [evalOrigin_mk] at ha
  exact isUnit_iff_ne_zero.mpr ha

end Origin

section Node

variable (k) in
/-- The node `x y`. -/
abbrev node : MvPolynomial (Fin 2) k := X 0 * X 1

variable (k) in
lemma eval_node : eval 0 (node k) = 0 := by simp

/-- **Check.** For the local ring `O` of the node `x y = 0` at the origin, over any field,
`Ω[O⁄k]` has no free quotient of nonzero rank. -/
theorem node_not_surjective {d : ℕ} (hd : d ≠ 0)
    (g : Ω[LocalRingAt (node k) (eval_node k)⁄k] →ₗ[LocalRingAt (node k) (eval_node k)]
      (Fin d → LocalRingAt (node k) (eval_node k))) : ¬ Function.Surjective g := by
  -- `(x, y) ↦ (t, 0)` and `(x, y) ↦ (0, t)` in `k⟦t⟧` separate `x` from `y`.
  have key : ∀ i j : Fin 2, i ≠ j →
      algebraMap (Curve k (node k)) (LocalRingAt (node k) (eval_node k))
          (Ideal.Quotient.mk _ (X i)) ∉
        Ideal.span {(algebraMap (Curve k (node k)) (LocalRingAt (node k) (eval_node k))
          (Ideal.Quotient.mk _ (X j)))} := by
    intro i j hij
    let p : Fin 2 → PowerSeries k := fun l ↦ if l = i then PowerSeries.X else 0
    have hp : ∀ l, PowerSeries.constantCoeff (p l) = 0 := fun l ↦ by
      by_cases h : l = i <;> simp [p, h]
    have hfp : aeval p (node k) = 0 := by
      fin_cases i <;> fin_cases j <;> simp_all [p]
    refine notMem_span_of_ringHom _ _ _ (isUnit_powerSeries _ (eval_node k) hp hfp) ?_
    simp [p, hij.symm, PowerSeries.X_ne_zero]
  exact not_surjective_kaehlerDifferential_of_mul_eq_zero (span_D_eq_top _ _)
    (by rw [← map_mul, ← map_mul]; simp) (key 0 1 (by decide)) (key 1 0 (by decide)) hd g

end Node

section Cusp

variable (k) in
/-- The cusp `y ^ 2 - x ^ 3`. -/
abbrev cusp : MvPolynomial (Fin 2) k := X 1 ^ 2 - X 0 ^ 3

variable (k) in
lemma eval_cusp : eval 0 (cusp k) = 0 := by simp

/-- In the local ring of the cusp, `y ∉ (x ^ 2)`: map to `k⟦t⟧` by `(x, y) ↦ (t ^ 2, t ^ 3)`. -/
lemma yc_notMem_span_xc_sq :
    yc (cusp k) (eval_cusp k) ∉ Ideal.span {xc (cusp k) (eval_cusp k) ^ 2} := by
  let p : Fin 2 → PowerSeries k := ![PowerSeries.X ^ 2, PowerSeries.X ^ 3]
  have hp : ∀ l, PowerSeries.constantCoeff (p l) = 0 := fun l ↦ by
    fin_cases l <;> simp [p]
  have hfp : aeval p (cusp k) = 0 := by simp [p, ← pow_mul]
  simp only [xc, yc, ← map_pow]
  refine notMem_span_of_ringHom _ _ _ (isUnit_powerSeries _ (eval_cusp k) hp hfp) ?_
  simp only [Ideal.mem_span_singleton, map_pow]
  simp only [AlgHom.toRingHom_eq_coe, Ideal.Quotient.lift_mk, RingHom.coe_coe, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, p, ← pow_mul]
  rw [PowerSeries.X_pow_dvd_iff]
  push Not
  exact ⟨3, by norm_num, by simp⟩

/-- In the local ring of the cusp, `x ^ 2 ∉ (y)`: map to `k[t] / (t ^ 3)` by `(x, y) ↦ (t, 0)`. -/
lemma xc_sq_notMem_span_yc :
    xc (cusp k) (eval_cusp k) ^ 2 ∉ Ideal.span {yc (cusp k) (eval_cusp k)} := by
  let I : Ideal (Polynomial k) := Ideal.span {Polynomial.X ^ 3}
  let p : Fin 2 → Polynomial k := ![Polynomial.X, 0]
  have hfp : aeval p (cusp k) ∈ I := by
    simp [p, cusp, I]
  let ψ : Curve k (cusp k) →+* Polynomial k ⧸ I :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp (aeval p).toRingHom) fun b hb ↦ by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      change Ideal.Quotient.mk I (aeval p (c * cusp k)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact I.mul_mem_left _ hfp
  have hψ : ∀ a, evalOrigin (cusp k) (eval_cusp k) a ≠ 0 → IsUnit (ψ a) := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    set q := aeval p b
    have hq0 : q.coeff 0 = eval 0 b := by
      have : (Polynomial.constantCoeff).comp (aeval p).toRingHom = eval 0 :=
        MvPolynomial.ringHom_ext (fun c ↦ by simp) (fun i ↦ by fin_cases i <;> simp [p])
      have h := RingHom.congr_fun this b
      rw [RingHom.comp_apply, Polynomial.constantCoeff_apply] at h
      exact h
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr (show (q - Polynomial.C (q.coeff 0)).coeff 0 = 0 by
      simp)
    have hnil : IsNilpotent (Ideal.Quotient.mk I (q - Polynomial.C (q.coeff 0))) :=
      ⟨3, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, hr, mul_pow]
             exact I.mul_mem_right _ (Ideal.mem_span_singleton_self _)⟩
    have hunit : IsUnit (Ideal.Quotient.mk I (Polynomial.C (q.coeff 0))) :=
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (hq0 ▸ ha))).map _
    have := hnil.isUnit_add_left_of_commute hunit (Commute.all _ _)
    rwa [← map_add, add_sub_cancel] at this
  simp only [xc, yc, ← map_pow]
  refine notMem_span_of_ringHom _ _ ψ hψ ?_
  simp only [map_pow, Ideal.mem_span_singleton]
  simp only [ψ, Ideal.Quotient.lift_mk, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, aeval_X, p, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, map_zero, zero_dvd_iff, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
    I, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  push Not
  exact ⟨2, by norm_num, by simp⟩

/-- **Check.** For the local ring `O` of the cusp `y ^ 2 = x ^ 3` at the origin, over a field in
which `2 ≠ 0` and `3 ≠ 0`, `Ω[O⁄k]` has no free quotient of nonzero rank. -/
theorem cusp_not_surjective (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) {d : ℕ} (hd : d ≠ 0)
    (g : Ω[LocalRingAt (cusp k) (eval_cusp k)⁄k] →ₗ[LocalRingAt (cusp k) (eval_cusp k)]
      (Fin d → LocalRingAt (cusp k) (eval_cusp k))) : ¬ Function.Surjective g := by
  have hu : ∀ c : k, c ≠ 0 → IsUnit (algebraMap k (LocalRingAt (cusp k) (eval_cusp k)) c) :=
    fun c hc ↦ (isUnit_iff_ne_zero.mpr hc).map _
  refine not_surjective_kaehlerDifferential_of_sq_eq_pow_three
    (by simpa only [map_ofNat] using hu 2 h2)
    (by simpa only [map_ofNat] using hu 3 h3) (span_D_eq_top _ _) ?_
    xc_sq_notMem_span_yc yc_notMem_span_xc_sq hd g
  rw [← map_pow, ← map_pow, ← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub, ← map_sub]
  simp

/-- **Check.** Over `ℚ`, the local ring of the cusp at the origin has no free quotient of its
differentials of rank one. -/
example (g : Ω[LocalRingAt (cusp ℚ) (eval_cusp ℚ)⁄ℚ] →ₗ[LocalRingAt (cusp ℚ) (eval_cusp ℚ)]
    (Fin 1 → LocalRingAt (cusp ℚ) (eval_cusp ℚ))) : ¬ Function.Surjective g :=
  cusp_not_surjective two_ne_zero three_ne_zero one_ne_zero g

end Cusp

end TauCeti.NodeCuspDifferentialsExample

end
