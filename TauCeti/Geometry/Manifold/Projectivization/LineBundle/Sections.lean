/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle
import Mathlib.Analysis.Calculus.Deriv.ZPow
import TauCeti.Analysis.Analytic.MultiIndex.Homogeneous
import TauCeti.Analysis.Complex.Hartogs
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# Holomorphic sections of `𝒪(k)` on complex projective space

This file computes the global holomorphic sections of the line bundles `𝒪(k)`
(`Projectivization.twistCore k`) on complex projective space `ℂℙⁿ = ℙ ℂ (Fin (n + 1) → ℂ)`.
For `k = d ≥ 0` they are exactly the sections `homogeneousSection d P` of the homogeneous
polynomials `P` of degree `d` (`Projectivization.mdifferentiable_section_twistCore_natCast_iff`),
so `H⁰(ℂℙⁿ, 𝒪(d))` is isomorphic to the space of homogeneous polynomials of degree `d` in `n + 1`
variables (`Projectivization.holomorphicTwistSectionsEquiv`) and has dimension
`binomial (n + d) n` (`Projectivization.finrank_holomorphicTwistSections`). For `k < 0` and
`n ≥ 1` the only holomorphic section is `0`
(`Projectivization.eq_zero_of_mdifferentiable_section_twistCore`). On the point `ℂℙ⁰` every
`𝒪(k)` is trivial, so the hypothesis `n ≠ 0` is needed there.

The proof is the transition-function and Hartogs argument. A section `s` of `𝒪(k)` defines on
`ℂⁿ⁺¹ \ {0}` the function `v ↦ s [v] * v a ^ k`, for `a` the preferred chart at `[v]`. On each
open set `v j ≠ 0` it is the coordinate of `s` in the frame of the chart `j`, read at the affine
coordinates of `[v]`, times `v j ^ k`, so it is holomorphic when `s` is; and it is homogeneous of
degree `k`. For `n ≥ 1` Hartogs' theorem extends it across the origin to an entire function. If
`k < 0`, homogeneity and continuity at the origin force it to vanish. If `k = d ≥ 0`, the
extension is homogeneous of degree `d` on all of `ℂⁿ⁺¹`, hence a homogeneous polynomial
(`AnalyticAt.exists_isHomogeneous_eval_eq`), and `s` is the section of that polynomial.

## Main declarations

* `Projectivization.holomorphicTwistSections n k`: the complex vector space `H⁰(ℂℙⁿ, 𝒪(k))` of
  holomorphic sections of `𝒪(k)`.
* `Projectivization.mdifferentiable_section_twistCore_natCast_iff`: a section of `𝒪(d)` is
  holomorphic exactly when it is the section of a homogeneous polynomial of degree `d`.
* `Projectivization.eq_zero_of_mdifferentiable_section_twistCore` and
  `Projectivization.holomorphicTwistSections_eq_bot`: `H⁰(ℂℙⁿ, 𝒪(k)) = 0` for `k < 0`, `n ≥ 1`.
* `Projectivization.holomorphicTwistSectionsEquiv`: `H⁰(ℂℙⁿ, 𝒪(d))` is isomorphic to the space
  of homogeneous polynomials of degree `d` in `n + 1` variables.
* `Projectivization.finrank_holomorphicTwistSections`: it has dimension `binomial (n + d) n`.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §1, for the sections
  of the hyperplane bundle and its powers through Hartogs' theorem.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter V, (15.5)–(15.6).
-/

public noncomputable section

open Bundle Filter Function MvPolynomial Set Topology
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable {n : ℕ}

/-! ### The space of holomorphic sections -/

/-- The complex vector space `H⁰(ℂℙⁿ, 𝒪(k))` of **holomorphic sections** of `𝒪(k)` on complex
projective space: the sections `s` for which `x ↦ (x, s x)` is a holomorphic map into the total
space of `𝒪(k)`. -/
def holomorphicTwistSections (n : ℕ) (k : ℤ) : Submodule ℂ (ℙ ℂ (Fin (n + 1) → ℂ) → ℂ) where
  carrier := {s | MDifferentiable 𝓘(ℂ, Fin n → ℂ) (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ))
    (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (n := n) k).Fiber) x (s x))}
  add_mem' hs ht := mdifferentiable_add_section hs ht
  zero_mem' := mdifferentiable_zeroSection ℂ (twistCore (𝕜 := ℂ) (n := n) k).Fiber
  smul_mem' _ _ hs := mdifferentiable_smul_const_section hs

theorem mem_holomorphicTwistSections {k : ℤ} {s : ℙ ℂ (Fin (n + 1) → ℂ) → ℂ} :
    s ∈ holomorphicTwistSections n k ↔ MDifferentiable 𝓘(ℂ, Fin n → ℂ)
      (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ))
      (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (n := n) k).Fiber) x (s x)) :=
  (Iff.rfl)

/-- The section of a homogeneous polynomial of degree `d` is a holomorphic section of `𝒪(d)`. -/
theorem homogeneousSection_mem_holomorphicTwistSections {d : ℕ}
    {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.IsHomogeneous d) :
    homogeneousSection d P ∈ holomorphicTwistSections n d :=
  (contMDiff_homogeneousSection hP 1).mdifferentiable one_ne_zero

/-! ### The homogeneous function of a section -/

/-- The homogeneous coordinate of the preferred chart of `𝒪(k)` at `x` does not vanish on the
chosen representative. -/
private theorem rep_indexAt_twistCore_ne_zero (k : ℤ) (x : ℙ ℂ (Fin (n + 1) → ℂ)) :
    x.rep ((twistCore (𝕜 := ℂ) k).indexAt x) ≠ 0 := by
  have hx := (twistCore (𝕜 := ℂ) (n := n) k).mem_baseSet_at x
  rwa [twistCore_baseSet, mem_affineOpen_iff] at hx

/-- The function on `ℂⁿ⁺¹` attached to a section `s` of `𝒪(k)`: at `v ≠ 0` it is `s [v] * v a ^ k`,
for `a` the preferred chart at `[v]`, and it is `0` at the origin. For the section of a
homogeneous polynomial it is the polynomial function away from the origin. -/
private def homogeneousLift (k : ℤ) (s : ℙ ℂ (Fin (n + 1) → ℂ) → ℂ) (v : Fin (n + 1) → ℂ) :
    ℂ :=
  if hv : v = 0 then 0 else s (mk ℂ v hv) * v ((twistCore (𝕜 := ℂ) k).indexAt (mk ℂ v hv)) ^ k

private theorem homogeneousLift_of_ne_zero (k : ℤ) (s : ℙ ℂ (Fin (n + 1) → ℂ) → ℂ)
    {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) :
    homogeneousLift k s v =
      s (mk ℂ v hv) * v ((twistCore (𝕜 := ℂ) k).indexAt (mk ℂ v hv)) ^ k := by
  simp only [homogeneousLift, hv, ↓reduceDIte]

/-- On the chosen representative of `x`, the homogeneous function of `s` is `s x` times the
`k`-th power of the coordinate of the preferred chart. -/
private theorem homogeneousLift_rep (k : ℤ) (s : ℙ ℂ (Fin (n + 1) → ℂ) → ℂ)
    (x : ℙ ℂ (Fin (n + 1) → ℂ)) :
    homogeneousLift k s x.rep = s x * x.rep ((twistCore (𝕜 := ℂ) k).indexAt x) ^ k := by
  rw [homogeneousLift_of_ne_zero k s x.rep_ne_zero, mk_rep]

/-- Where `v j ≠ 0`, the homogeneous function of `s` is the coordinate of `s` in the frame of the
chart `j` at `[v]`, times `v j ^ k`. -/
private theorem homogeneousLift_eq_twistTransition_mul (k : ℤ) (s : ℙ ℂ (Fin (n + 1) → ℂ) → ℂ)
    {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) {j : Fin (n + 1)} (hj : v j ≠ 0) :
    homogeneousLift k s v = twistTransition k ((twistCore (𝕜 := ℂ) k).indexAt (mk ℂ v hv)) j
      (mk ℂ v hv) * s (mk ℂ v hv) * v j ^ k := by
  have ha : v ((twistCore (𝕜 := ℂ) k).indexAt (mk ℂ v hv)) ≠ 0 := by
    have hx := (twistCore (𝕜 := ℂ) (n := n) k).mem_baseSet_at (mk ℂ v hv)
    rwa [twistCore_baseSet, mk_mem_affineOpen_iff] at hx
  rw [homogeneousLift_of_ne_zero k s hv, twistTransition_mk, div_zpow]
  field_simp

/-- The homogeneous function of a section of `𝒪(k)` is homogeneous of degree `k`. -/
private theorem homogeneousLift_smul (k : ℤ) (s : ℙ ℂ (Fin (n + 1) → ℂ) → ℂ) {t : ℂ}
    (ht : t ≠ 0) (v : Fin (n + 1) → ℂ) :
    homogeneousLift k s (t • v) = t ^ k * homogeneousLift k s v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [homogeneousLift]
  have htv : t • v ≠ 0 := smul_ne_zero ht hv
  have hmk : mk ℂ (t • v) htv = mk ℂ v hv := (mk_eq_mk_iff' ℂ _ _ htv hv).2 ⟨t, rfl⟩
  rw [homogeneousLift_of_ne_zero k s htv, homogeneousLift_of_ne_zero k s hv, hmk, Pi.smul_apply,
    smul_eq_mul, mul_zpow]
  ring

/-- The coordinate of a holomorphic section of `𝒪(k)` in the frame of the chart `j`, read in the
affine coordinates of that chart, is an entire function. -/
private theorem differentiable_twistTransition_mul_comp_affineChart_symm {k : ℤ}
    {s : ℙ ℂ (Fin (n + 1) → ℂ) → ℂ} (hs : s ∈ holomorphicTwistSections n k) (j : Fin (n + 1)) :
    Differentiable ℂ ((fun x ↦ twistTransition k ((twistCore (𝕜 := ℂ) k).indexAt x) j x * s x) ∘
      (affineChart j).symm) := by
  intro z
  have hz : (affineChart (K := ℂ) j).symm z ∈ affineOpen j := by simp
  let s' : ∀ x, (twistCore (𝕜 := ℂ) (n := n) k).Fiber x := s
  have : MemTrivializationAtlas ((twistCore (𝕜 := ℂ) (n := n) k).localTriv j) := ⟨⟨j, rfl⟩⟩
  have hcoord := (((twistCore (𝕜 := ℂ) (n := n) k).localTriv j).mdifferentiableAt_section_iff
    𝓘(ℂ, Fin n → ℂ) s' (by rwa [twistCore_localTriv_baseSet])).1
    (mem_holomorphicTwistSections.1 hs _)
  rw [show (fun x ↦ (((twistCore k).localTriv j) ⟨x, s' x⟩).2) =
    fun x ↦ twistTransition k ((twistCore (𝕜 := ℂ) k).indexAt x) j x * s x from
    funext fun x ↦ twistCore_localTriv_apply k j s x] at hcoord
  exact mdifferentiableAt_iff_differentiableAt.1
    (hcoord.comp z ((contMDiff_affineChart_symm j 1).mdifferentiable one_ne_zero z))

/-- The homogeneous function of a holomorphic section of `𝒪(k)` is holomorphic away from the
origin. -/
private theorem differentiableOn_homogeneousLift {k : ℤ} {s : ℙ ℂ (Fin (n + 1) → ℂ) → ℂ}
    (hs : s ∈ holomorphicTwistSections n k) : DifferentiableOn ℂ (homogeneousLift k s) {0}ᶜ := by
  intro v hv
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (show v ≠ 0 from hv)
  -- Near `v`, the function is the chart-`j` coordinate of `s` at the affine coordinates of `[w]`,
  -- times `w j ^ k`.
  have hcoord (i : Fin (n + 1)) : DifferentiableAt ℂ (fun w : Fin (n + 1) → ℂ ↦ w i) v :=
    differentiableAt_pi.1 differentiableAt_id i
  have hratio : DifferentiableAt ℂ (fun w : Fin (n + 1) → ℂ ↦ fun l ↦ w (j.succAbove l) / w j) v :=
    differentiableAt_pi.2 fun l ↦ ((hcoord _).mul ((hcoord j).inv hj)).congr_of_eventuallyEq
      (Eventually.of_forall fun w ↦ div_eq_mul_inv _ _)
  have hmain := ((differentiable_twistTransition_mul_comp_affineChart_symm hs j _).comp v
    hratio).mul ((differentiableAt_zpow (m := k).2 (Or.inl hj)).comp v (hcoord j))
  refine (hmain.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [((continuous_apply j).isOpen_preimage _ isOpen_ne).mem_nhds hj] with w hw
  have hw0 : w ≠ 0 := fun h ↦ hw (by simp [h])
  have hmk : (affineChart j).symm (fun l ↦ w (j.succAbove l) / w j) = mk ℂ w hw0 := by
    rw [affineChart_symm_apply, mk_eq_mk_iff']
    exact ⟨(w j)⁻¹, (Fin.insertNth_one_div_eq_inv_smul j w hw).symm⟩
  rw [homogeneousLift_eq_twistTransition_mul k s hw0 hw, Pi.mul_apply, comp_apply, comp_apply,
    comp_apply, hmk]

/-- **Hartogs extension of the homogeneous function.** For `n ≥ 1` the homogeneous function of a
holomorphic section of `𝒪(k)` agrees off the origin with an analytic function on `ℂⁿ⁺¹`. -/
private theorem exists_analyticOnNhd_eqOn_homogeneousLift (hn : n ≠ 0) {k : ℤ}
    {s : ℙ ℂ (Fin (n + 1) → ℂ) → ℂ} (hs : s ∈ holomorphicTwistSections n k) :
    ∃ G : (Fin (n + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ G univ ∧ EqOn G (homogeneousLift k s) {0}ᶜ := by
  have hdim : 2 ≤ Module.finrank ℂ (Fin (n + 1) → ℂ) := by
    rw [Module.finrank_fin_fun]
    omega
  obtain ⟨G, hG, hGeq⟩ := TauCeti.exists_analyticOnNhd_eqOn_sdiff_singleton hdim isOpen_univ 0
    (by simpa [compl_eq_univ_sdiff] using differentiableOn_homogeneousLift hs)
  exact ⟨G, hG, by simpa [compl_eq_univ_sdiff] using hGeq⟩

/-- For `k = d ≥ 0` the homogeneous function of a holomorphic section of `𝒪(d)` is, away from the
origin, a homogeneous polynomial of degree `d`. On `ℂℙ⁰` this holds for every section. -/
private theorem exists_isHomogeneous_eval_eq_homogeneousLift (d : ℕ)
    {s : ℙ ℂ (Fin (n + 1) → ℂ) → ℂ} (hs : s ∈ holomorphicTwistSections n d) :
    ∃ P : MvPolynomial (Fin (n + 1)) ℂ, P.IsHomogeneous d ∧
      ∀ v, v ≠ 0 → eval v P = homogeneousLift d s v := by
  rcases eq_or_ne n 0 with rfl | hn
  · -- On a point, `v = v 0 • 1` and homogeneity gives the monomial `c * X 0 ^ d`.
    refine ⟨C (homogeneousLift d s 1) * X 0 ^ d, isHomogeneous_C_mul_X_pow _ _ _, fun v hv ↦ ?_⟩
    have hv0 : v 0 ≠ 0 := fun h ↦ hv (funext fun i ↦ by rw [Fin.fin_one_eq_zero i, h]; rfl)
    have hvsmul : v = v 0 • (1 : Fin 1 → ℂ) := funext fun i ↦ by
      simp [Fin.fin_one_eq_zero i]
    rw [hvsmul, homogeneousLift_smul _ s hv0]
    simp [mul_comm]
  · obtain ⟨G, hG, hGeq⟩ := exists_analyticOnNhd_eqOn_homogeneousLift hn hs
    have hGcont : Continuous G := hG.continuous
    -- `G` is homogeneous off the origin, hence everywhere by density and continuity.
    have hhom : ∀ (t : ℂ) v, G (t • v) = t ^ d * G v := by
      have hdense : Dense ({(0 : ℂ)}ᶜ ×ˢ {(0 : Fin (n + 1) → ℂ)}ᶜ) :=
        (dense_compl_singleton _).prod (dense_compl_singleton _)
      have := Continuous.ext_on hdense (f := fun p : ℂ × (Fin (n + 1) → ℂ) ↦ G (p.1 • p.2))
        (g := fun p ↦ p.1 ^ d * G p.2) (hGcont.comp (continuous_fst.smul continuous_snd))
        ((continuous_fst.pow d).mul (hGcont.comp continuous_snd)) fun p ⟨ht, hv⟩ ↦ by
          have ht : p.1 ≠ 0 := ht
          have hv : p.2 ≠ 0 := hv
          dsimp only
          rw [hGeq (smul_ne_zero ht hv), hGeq hv, homogeneousLift_smul _ s ht, zpow_natCast]
      exact fun t v ↦ congrFun this (t, v)
    obtain ⟨P, hP, hPeval⟩ := (hG 0 trivial).exists_isHomogeneous_eval_eq hhom
    exact ⟨P, hP, fun v hv ↦ (hPeval v).trans (hGeq hv)⟩

/-! ### Holomorphic sections of `𝒪(k)` -/

/-- **`H⁰(ℂℙⁿ, 𝒪(k)) = 0` for `k < 0`.** For `n ≥ 1` and `k < 0`, the only holomorphic section of
`𝒪(k)` on `ℂℙⁿ` is zero. -/
theorem eq_zero_of_mdifferentiable_section_twistCore (hn : n ≠ 0) {k : ℤ} (hk : k < 0)
    {s : ℙ ℂ (Fin (n + 1) → ℂ) → ℂ}
    (hs : MDifferentiable 𝓘(ℂ, Fin n → ℂ) (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ))
      (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore k).Fiber) x (s x))) :
    s = 0 := by
  obtain ⟨G, hG, hGeq⟩ :=
    exists_analyticOnNhd_eqOn_homogeneousLift hn (mem_holomorphicTwistSections.2 hs)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -(m + 1 : ℕ) := ⟨(-k - 1).toNat, by omega⟩
  -- `G v = t ^ (m + 1) * G (t • v)` for `t ≠ 0`; letting `t → 0` gives `G v = 0`.
  have hG0 (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) : G v = 0 := by
    have hcont : Continuous fun t : ℂ ↦ t ^ (m + 1) * G (t • v) :=
      (continuous_pow _).mul (hG.continuous.comp (continuous_id.smul continuous_const))
    have := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) (g := fun _ ↦ G v) hcont
      continuous_const
      fun t (ht : t ≠ 0) ↦ by
        rw [hGeq (smul_ne_zero ht hv), hGeq hv, homogeneousLift_smul _ s ht, hm, zpow_neg,
          zpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht), one_mul]
    simpa using (congrFun this 0).symm
  funext x
  have hlift := homogeneousLift_rep k s x
  rw [← hGeq (by simpa using x.rep_ne_zero), hG0 _ x.rep_ne_zero] at hlift
  exact (mul_eq_zero.1 hlift.symm).resolve_right
    (zpow_ne_zero _ (rep_indexAt_twistCore_ne_zero k x))

/-- **Holomorphic sections of `𝒪(d)` are homogeneous polynomials.** A section of `𝒪(d)` on
`ℂℙⁿ`, for `d ≥ 0`, is holomorphic exactly when it is the section `homogeneousSection d P` of a
homogeneous polynomial `P` of degree `d`. -/
theorem mdifferentiable_section_twistCore_natCast_iff (d : ℕ) (s : ℙ ℂ (Fin (n + 1) → ℂ) → ℂ) :
    MDifferentiable 𝓘(ℂ, Fin n → ℂ) (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ))
        (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (d : ℤ)).Fiber) x (s x)) ↔
      ∃ P : MvPolynomial (Fin (n + 1)) ℂ, P.IsHomogeneous d ∧ homogeneousSection d P = s := by
  refine ⟨fun hs ↦ ?_, fun ⟨P, hP, hPs⟩ ↦
    mem_holomorphicTwistSections.1 (hPs ▸ homogeneousSection_mem_holomorphicTwistSections hP)⟩
  obtain ⟨P, hP, hPeval⟩ :=
    exists_isHomogeneous_eval_eq_homogeneousLift d (mem_holomorphicTwistSections.2 hs)
  refine ⟨P, hP, funext fun x ↦ ?_⟩
  rw [homogeneousSection_def, hPeval _ x.rep_ne_zero, homogeneousLift_rep, zpow_natCast,
    mul_div_cancel_right₀ _ (pow_ne_zero _ (rep_indexAt_twistCore_ne_zero _ x))]

/-- `H⁰(ℂℙⁿ, 𝒪(k)) = 0` for `n ≥ 1` and `k < 0`. -/
theorem holomorphicTwistSections_eq_bot (hn : n ≠ 0) {k : ℤ} (hk : k < 0) :
    holomorphicTwistSections n k = ⊥ :=
  (Submodule.eq_bot_iff _).2 fun _ hs ↦
    eq_zero_of_mdifferentiable_section_twistCore hn hk (mem_holomorphicTwistSections.1 hs)

/-- The holomorphic sections of `𝒪(d)` are exactly the sections of the homogeneous polynomials of
degree `d`. -/
theorem mem_holomorphicTwistSections_natCast_iff (d : ℕ) {s : ℙ ℂ (Fin (n + 1) → ℂ) → ℂ} :
    s ∈ holomorphicTwistSections n d ↔
      ∃ P : MvPolynomial (Fin (n + 1)) ℂ, P.IsHomogeneous d ∧ homogeneousSection d P = s := by
  rw [mem_holomorphicTwistSections, mdifferentiable_section_twistCore_natCast_iff]

/-- The section map from homogeneous polynomials of degree `d` to holomorphic sections of
`𝒪(d)`. -/
private def homogeneousSectionLinearMap (d : ℕ) :
    homogeneousSubmodule (Fin (n + 1)) ℂ d →ₗ[ℂ] holomorphicTwistSections n d where
  toFun P := ⟨homogeneousSection d P, homogeneousSection_mem_holomorphicTwistSections P.2⟩
  map_add' P Q := by ext1; simp
  map_smul' c P := by ext1; simp

private theorem bijective_homogeneousSectionLinearMap (d : ℕ) :
    Bijective (homogeneousSectionLinearMap (n := n) d) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun P hP ↦ ?_, fun s ↦ ?_⟩
  · have hP' : homogeneousSection d (P : MvPolynomial (Fin (n + 1)) ℂ) = 0 :=
      congrArg Subtype.val hP
    exact Subtype.ext ((homogeneousSection_eq_zero_iff P.2).1 hP')
  · obtain ⟨P, hP, hPs⟩ := (mem_holomorphicTwistSections_natCast_iff d).1 s.2
    exact ⟨⟨P, hP⟩, Subtype.ext hPs⟩

/-- **`H⁰(ℂℙⁿ, 𝒪(d))` is the space of homogeneous polynomials of degree `d`.** The holomorphic
sections of `𝒪(d)` on `ℂℙⁿ` correspond to the homogeneous polynomials of degree `d` in `n + 1`
variables, the polynomial `P` corresponding to `homogeneousSection d P`. -/
def holomorphicTwistSectionsEquiv (n d : ℕ) :
    holomorphicTwistSections n d ≃ₗ[ℂ] homogeneousSubmodule (Fin (n + 1)) ℂ d :=
  (LinearEquiv.ofBijective _ (bijective_homogeneousSectionLinearMap d)).symm

/-- The holomorphic section corresponding to a homogeneous polynomial is its section. -/
@[simp]
theorem coe_holomorphicTwistSectionsEquiv_symm_apply (d : ℕ)
    (P : homogeneousSubmodule (Fin (n + 1)) ℂ d) :
    ((holomorphicTwistSectionsEquiv n d).symm P : ℙ ℂ (Fin (n + 1) → ℂ) → ℂ) =
      homogeneousSection d P :=
  (rfl)

/-- A holomorphic section of `𝒪(d)` is the section of its corresponding homogeneous
polynomial. -/
@[simp]
theorem homogeneousSection_holomorphicTwistSectionsEquiv_apply (d : ℕ)
    (s : holomorphicTwistSections n d) :
    homogeneousSection d (holomorphicTwistSectionsEquiv n d s : MvPolynomial (Fin (n + 1)) ℂ) =
      s := by
  rw [← coe_holomorphicTwistSectionsEquiv_symm_apply, LinearEquiv.symm_apply_apply]

/-- **The dimension of `H⁰(ℂℙⁿ, 𝒪(d))`.** The holomorphic sections of `𝒪(d)` on `ℂℙⁿ` form a
complex vector space of dimension `binomial (n + d) n`. -/
theorem finrank_holomorphicTwistSections (n d : ℕ) :
    Module.finrank ℂ (holomorphicTwistSections n d) = (n + d).choose n := by
  rw [(holomorphicTwistSectionsEquiv n d).finrank_eq,
    TauCeti.finrank_homogeneousSubmodule_eq_multichoose]
  simpa [Nat.multichoose_eq, Nat.add_right_comm] using Nat.choose_symm_add.symm

/-- The holomorphic sections of `𝒪(k)` on `ℂℙⁿ` form a space of dimension `0` when `n ≥ 1` and
`k < 0`. -/
theorem finrank_holomorphicTwistSections_of_neg (hn : n ≠ 0) {k : ℤ} (hk : k < 0) :
    Module.finrank ℂ (holomorphicTwistSections n k) = 0 := by
  rw [holomorphicTwistSections_eq_bot hn hk, finrank_bot]

end Projectivization
