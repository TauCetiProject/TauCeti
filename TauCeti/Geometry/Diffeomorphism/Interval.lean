/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.FixingSubgroup.Basic
public import TauCeti.Geometry.Diffeomorphism.Topology
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Topology.Homotopy.Contractible
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Icc
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.WithSeminorms
import TauCeti.Geometry.Manifold.Instances.Icc
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Diffeomorphisms of an interval that are the identity near its ends

The `C^n` diffeomorphisms of a closed interval `[a, b]`, `a < b`, `n ≠ 0`, that are the identity
on a neighbourhood of the two endpoints form a contractible space for the weak Whitney topology.
This is the one-dimensional case of Smale's theorem that the diffeomorphisms of the square `[0, 1]²`
equal to the identity near the boundary form a contractible space. The contraction is the straight
line to the identity: at time `t ∈ [0, 1]` a diffeomorphism `f` is moved to

`x ↦ (1 - t) f x + t x`

(`TauCeti.straightenIcc`). The contraction is smooth in the time parameter and the point jointly
(`TauCeti.contMDiff_straightenIcc`), it fixes the identity at all times, and it is continuous in
the diffeomorphism (`TauCeti.continuous_straightenIcc`).

Each intermediate map is a diffeomorphism. Extend the displacement `x ↦ f x - x` of `f` by zero to
all of `ℝ`, which is `C^n` because it vanishes near both endpoints, and write `F x = x + d x`.
Then `F` is a bijection of `ℝ` with inverse given by the displacement of `f⁻¹`, so its derivative
never vanishes; it is `1` far out, so it is positive everywhere. Hence
`x ↦ x + (1 - t) d x = (1 - t) F x + t x` has positive derivative and is the identity far out,
so it is a homeomorphism of `ℝ` with `C^n` inverse by the inverse function theorem
(`Homeomorph.contDiff_symm_deriv`), and it restricts to a diffeomorphism of `[a, b]`.

Continuity in the diffeomorphism is checked on the real functions: composition with the inclusion
`[a, b] → ℝ` is an embedding of the interval-valued `C^n` maps into the real ones
(`ContMDiffMap.isEmbedding_subtypeValIcc_comp`), and on real functions the contraction is the
affine expression `x ↦ x + (1 - t) (f x - x)`.

## Main definitions

* `TauCeti.straightenIcc`: the straight-line contraction `x ↦ (1 - t) f x + t x` of a
  diffeomorphism of `[a, b]` equal to the identity near both endpoints.
* `TauCeti.straighteningHomotopyIcc`: the contraction as a homotopy from the identity to the
  constant map at the identity, fixing the identity.

## Main results

* `TauCeti.continuous_straightenIcc`: the contraction is jointly continuous.
* `TauCeti.contractibleSpace_nhdsFixingSubgroup_Icc`: the diffeomorphisms of `[a, b]` equal to
  the identity near the endpoints form a contractible space.

## References

* S. Smale, *Diffeomorphisms of the 2-sphere*, Proc. Amer. Math. Soc. 10 (1959), 621–626.
-/

public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney TauCeti.ManifoldWeakWhitney

namespace TauCeti

variable {a b : ℝ} [Fact (a < b)] {n : ℕ∞ω}

/-- The displacement `x ↦ f x - x` of a self-map of `[a, b]`, extended to `ℝ` by its values at the
endpoints. -/
private def displacementIcc (f : Icc a b → Icc a b) : ℝ → ℝ :=
  IccExtend (Fact.out : a < b).le fun p ↦ (f p : ℝ) - p

private theorem displacementIcc_val (f : Icc a b → Icc a b) (p : Icc a b) :
    displacementIcc f p = (f p : ℝ) - p :=
  IccExtend_val _ _ p

/-- A diffeomorphism of `[a, b]` equal to the identity near both endpoints is the identity within
some distance `ε` of them. -/
private theorem exists_pos_forall_apply_eq {f : Icc a b ≃ₘ^n⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc a b}
    (hf : f ∈ Diffeomorph.nhdsFixingSubgroup ((𝓡∂ 1).boundary (Icc a b))) :
    ∃ ε > 0, ∀ p : Icc a b, ((p : ℝ) < a + ε ∨ b - ε < p) → f p = p := by
  rw [Diffeomorph.mem_nhdsFixingSubgroup_iff, boundary_Icc, nhdsSet_insert, nhdsSet_singleton,
    eventually_sup] at hf
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.eventually_nhds_iff.mp hf.1
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.eventually_nhds_iff.mp hf.2
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun p hp ↦ ?_⟩
  have hp₁ := p.property.1
  have hp₂ := p.property.2
  rcases hp with hp | hp
  · refine h₁ ?_
    rw [Subtype.dist_eq, Real.dist_eq, Set.Icc.coe_bot, abs_of_nonneg (by linarith)]
    linarith [min_le_left ε₁ ε₂]
  · refine h₂ ?_
    rw [Subtype.dist_eq, Real.dist_eq, Set.Icc.coe_top, abs_of_nonpos (by linarith)]
    linarith [min_le_right ε₁ ε₂]

/-- The displacement of a diffeomorphism equal to the identity near the endpoints vanishes within
some distance `ε` of them, and outside `[a, b]`, and it is `C^n`. -/
private theorem exists_displacementIcc {f : Icc a b ≃ₘ^n⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc a b}
    (hf : f ∈ Diffeomorph.nhdsFixingSubgroup ((𝓡∂ 1).boundary (Icc a b))) :
    ContDiff ℝ n (displacementIcc f) ∧
      ∃ ε > 0, ∀ x, (x < a + ε ∨ b - ε < x) → displacementIcc f x = 0 := by
  obtain ⟨ε, hε, hfε⟩ := exists_pos_forall_apply_eq hf
  have hzero : ∀ x, (x < a + ε ∨ b - ε < x) → displacementIcc f x = 0 := by
    intro x hx
    rw [displacementIcc, IccExtend_apply, hfε, sub_self]
    rcases hx with hx | hx
    · exact Or.inl (max_lt (by linarith) ((min_le_right _ _).trans_lt hx))
    · exact Or.inr (lt_max_of_lt_right (lt_min (by linarith) hx))
  refine ⟨contDiff_iff_contDiffAt.mpr fun x ↦ ?_, ε, hε, hzero⟩
  by_cases hx : x < a + ε ∨ b - ε < x
  · -- Near such a point the displacement is zero.
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    rcases hx with hx | hx
    · filter_upwards [Iio_mem_nhds hx] with y hy using hzero y (Or.inl hy)
    · filter_upwards [Ioi_mem_nhds hx] with y hy using hzero y (Or.inr hy)
  · -- Otherwise `x` is interior, where the displacement is a smooth map read through `projIcc`.
    push Not at hx
    have hxI : Icc a b ∈ 𝓝 x := Icc_mem_nhds (by linarith) (by linarith)
    have hg : ContMDiff (𝓡∂ 1) 𝓘(ℝ) n fun p : Icc a b ↦ (f p : ℝ) - p :=
      (contMDiff_subtypeVal_Icc.comp f.contMDiff).sub contMDiff_subtypeVal_Icc
    have hon := (contMDiffOn_comp_projIcc_iff.mpr hg).contDiffOn
    exact (hon.contDiffAt hxI).congr_of_eventuallyEq (Eventually.of_forall fun y ↦ by
      rw [displacementIcc, IccExtend])

/-- The extended map `x ↦ x + d x` of a diffeomorphism equal to the identity near the endpoints
has positive derivative: its inverse is the extended map of the inverse diffeomorphism, so its
derivative never vanishes, and the derivative is `1` far out. -/
private theorem one_add_deriv_displacementIcc_pos (hn : n ≠ 0)
    {f : Icc a b ≃ₘ^n⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc a b}
    (hf : f ∈ Diffeomorph.nhdsFixingSubgroup ((𝓡∂ 1).boundary (Icc a b))) (x : ℝ) :
    0 < 1 + deriv (displacementIcc f) x := by
  obtain ⟨hd, ε, hε, hzero⟩ := exists_displacementIcc hf
  obtain ⟨hd', ε', hε', hzero'⟩ := exists_displacementIcc (inv_mem hf)
  set d := displacementIcc f with hd_def
  set d' := displacementIcc ⇑f⁻¹ with hd'_def
  -- `y ↦ y + d' y` inverts `y ↦ y + d y`.
  have hinv (y : ℝ) : y + d y + d' (y + d y) = y := by
    by_cases hy : y ∈ Icc a b
    · lift y to Icc a b using hy with p
      have hfy : (p : ℝ) + d p = f p := by
        rw [hd_def, displacementIcc_val]
        ring
      rw [hfy, hd'_def, displacementIcc_val, Diffeomorph.inv_apply, Diffeomorph.symm_apply_apply]
      ring
    · -- A point outside `[a, b]` is within every positive distance `δ` of an end.
      have hout (δ : ℝ) (hδ : 0 < δ) : y < a + δ ∨ b - δ < y := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hy
        exact hy.imp (fun h ↦ by linarith) fun h ↦ by linarith
      rw [hzero y (hout ε hε), add_zero, hzero' y (hout ε' hε'), add_zero]
  have hdiff (y : ℝ) : HasDerivAt (fun y ↦ y + d y) (1 + deriv d y) y :=
    (hasDerivAt_id y).add ((hd.differentiable hn y).hasDerivAt)
  have hdiff' (y : ℝ) : HasDerivAt (fun y ↦ y + d' y) (1 + deriv d' y) y :=
    (hasDerivAt_id y).add ((hd'.differentiable hn y).hasDerivAt)
  -- So the derivative of `y ↦ y + d y` never vanishes.
  have hne (y : ℝ) : 1 + deriv d y ≠ 0 := by
    have hcomp := (hdiff' (y + d y)).comp y (hdiff y)
    have hid : HasDerivAt ((fun y ↦ y + d' y) ∘ fun y ↦ y + d y) 1 y := by
      convert hasDerivAt_id y using 1
      funext z
      exact hinv z
    intro h0
    rw [h0, mul_zero] at hcomp
    exact zero_ne_one (hcomp.unique hid)
  -- It is `1` to the left of `[a, b]`, hence positive everywhere by the intermediate value theorem.
  have hone : 1 + deriv d (a - 1) = 1 := by
    have ha : a - 1 < a + ε := by linarith
    have : d =ᶠ[𝓝 (a - 1)] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds ha] with y hy
      exact hzero y (Or.inl hy)
    rw [this.deriv_eq, deriv_const, add_zero]
  have hcont : Continuous fun y ↦ 1 + deriv d y :=
    continuous_const.add (hd.continuous_deriv (ENat.one_le_iff_ne_zero_withTop.mpr hn))
  by_contra hx
  obtain ⟨y, hy⟩ := intermediate_value_univ x (a - 1) hcont
    ⟨not_lt.mp hx, by rw [hone]; exact zero_le_one⟩
  exact hne y hy

/-- The real straight-line map `x ↦ x + (1 - t) d x`, from the extended map of `f` at `t = 0` to the
identity at `t = 1`. -/
private def straightenReal (f : Icc a b → Icc a b) (t : ℝ) (x : ℝ) : ℝ :=
  x + (1 - t) * displacementIcc f x

/-- For a diffeomorphism equal to the identity near the endpoints and `t ∈ [0, 1]`, the real
straight-line map is an order isomorphism of `ℝ` with `C^n` inverse, fixing `a` and `b`. -/
private theorem exists_orderIso_straightenReal (hn : n ≠ 0)
    {f : Icc a b ≃ₘ^n⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc a b}
    (hf : f ∈ Diffeomorph.nhdsFixingSubgroup ((𝓡∂ 1).boundary (Icc a b))) (t : unitInterval) :
    ∃ e : ℝ ≃o ℝ, ⇑e = straightenReal f t ∧ ContDiff ℝ n e.symm ∧ e a = a ∧ e b = b := by
  obtain ⟨hd, ε, hε, hzero⟩ := exists_displacementIcc hf
  set F := straightenReal f t with hF_def
  have hF : ContDiff ℝ n F := contDiff_id.add (contDiff_const.mul hd)
  have hderiv (x : ℝ) : HasDerivAt F (1 + (1 - t) * deriv (displacementIcc f) x) x :=
    (hasDerivAt_id x).add (((hd.differentiable hn x).hasDerivAt).const_mul _)
  have hpos (x : ℝ) : 0 < 1 + (1 - t) * deriv (displacementIcc f) x := by
    have h := one_add_deriv_displacementIcc_pos hn hf x
    have ht0 := t.property.1
    have ht1 := t.property.2
    rcases ht1.lt_or_eq with ht1 | ht1
    · nlinarith
    · rw [ht1, sub_self, zero_mul, add_zero]
      exact zero_lt_one
  have hfix (x : ℝ) (hx : x < a + ε ∨ b - ε < x) : F x = x := by
    rw [hF_def, straightenReal, hzero x hx, mul_zero, add_zero]
  have hmono : StrictMono F := strictMono_of_deriv_pos fun x ↦ (hderiv x).deriv ▸ hpos x
  have hsurj : Function.Surjective F := hF.continuous.surjective
    (tendsto_id.congr' ((eventually_gt_atTop (b - ε)).mono fun x hx ↦ (hfix x (Or.inr hx)).symm))
    (tendsto_id.congr' ((eventually_lt_atBot (a + ε)).mono fun x hx ↦ (hfix x (Or.inl hx)).symm))
  set e := hmono.orderIsoOfSurjective F hsurj
  have he : ⇑e = F := hmono.coe_orderIsoOfSurjective F hsurj
  refine ⟨e, he, ?_, he ▸ hfix a (Or.inl (by linarith)), he ▸ hfix b (Or.inr (by linarith))⟩
  have hsymm := e.toHomeomorph.contDiff_symm_deriv (fun x ↦ (hpos x).ne')
    (by rw [OrderIso.coe_toHomeomorph, he]; exact hderiv)
    (by rw [OrderIso.coe_toHomeomorph, he]; exact hF)
  rwa [OrderIso.coe_toHomeomorph_symm] at hsymm

/-- The straight-line map `x ↦ (1 - t) f x + t x`, `t ∈ [0, 1]`, of a diffeomorphism of `[a, b]`
equal to the identity near the endpoints is a diffeomorphism. -/
private theorem exists_diffeomorph_convexComb (hn : n ≠ 0)
    {f : Icc a b ≃ₘ^n⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc a b}
    (hf : f ∈ Diffeomorph.nhdsFixingSubgroup ((𝓡∂ 1).boundary (Icc a b))) (t : unitInterval) :
    ∃ g : Icc a b ≃ₘ^n⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc a b, ∀ p, g p = Icc.convexComb (f p) p t := by
  obtain ⟨e, he, he', hea, heb⟩ := exists_orderIso_straightenReal hn hf t
  have hF (p : Icc a b) : e p = (Icc.convexComb (f p) p t : ℝ) := by
    rw [he, Icc.coe_convexComb, straightenReal, displacementIcc_val]
    ring
  -- Restrict `e` to `[a, b] ≃ [e a, e b]`, which is `[a, b]` since `e` fixes both endpoints.
  set r : Icc a b ≃ Icc a b :=
    (e.Icc a b).toEquiv.trans (Set.equivOfEq (by rw [hea, heb]))
  -- `OrderIso.Icc` has no application lemmas; its two directions act as `e` and `e.symm`.
  have hr (p : Icc a b) : (r p : ℝ) = e p := (rfl)
  have hr' (p : Icc a b) : (r.symm p : ℝ) = e.symm p := (rfl)
  have hval (p : Icc a b) : r p = Icc.convexComb (f p) p t := Subtype.ext ((hr p).trans (hF p))
  have hinv : ContMDiff (𝓡∂ 1) 𝓘(ℝ) n fun p : Icc a b ↦ (r.symm p : ℝ) := by
    simp only [hr']
    exact he'.contMDiff.comp contMDiff_subtypeVal_Icc
  refine ⟨{ toEquiv := r
            contMDiff_toFun := (ContMDiff.convexComb f.contMDiff contMDiff_id contMDiff_const).congr
              hval
            contMDiff_invFun := contMDiff_iff_comp_subtypeVal_Icc.mpr
              ⟨continuous_induced_rng.mpr hinv.continuous, hinv⟩ }, hval⟩

/-- **The straight-line contraction of the diffeomorphisms of an interval that are the identity
near its endpoints.** For `n ≠ 0`, a `C^n` diffeomorphism `f` of `[a, b]` equal to the identity
near both endpoints and a time `t ∈ [0, 1]` give the diffeomorphism `x ↦ (1 - t) f x + t x`
(`TauCeti.straightenIcc_apply`), again equal to the identity near the endpoints. It is `f` at time
`0` and the identity at time `1`. -/
def straightenIcc (hn : n ≠ 0)
    (f : Diffeomorph.nhdsFixingSubgroup (I := 𝓡∂ 1) (n := n) ((𝓡∂ 1).boundary (Icc a b)))
    (t : unitInterval) :
    Diffeomorph.nhdsFixingSubgroup (I := 𝓡∂ 1) (n := n) ((𝓡∂ 1).boundary (Icc a b)) :=
  ⟨(exists_diffeomorph_convexComb hn f.property t).choose, by
    rw [Diffeomorph.mem_nhdsFixingSubgroup_iff]
    filter_upwards [Diffeomorph.mem_nhdsFixingSubgroup_iff.mp f.property] with p hp
    rw [(exists_diffeomorph_convexComb hn f.property t).choose_spec p, hp, Icc.convexComb_eq]⟩

/-- The straight-line contraction at time `t` is `x ↦ (1 - t) f x + t x`. -/
@[simp]
theorem straightenIcc_apply (hn : n ≠ 0)
    (f : Diffeomorph.nhdsFixingSubgroup (I := 𝓡∂ 1) (n := n) ((𝓡∂ 1).boundary (Icc a b)))
    (t : unitInterval) (p : Icc a b) :
    (straightenIcc hn f t : Icc a b ≃ₘ^n⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc a b) p =
      Icc.convexComb ((f : Icc a b ≃ₘ^n⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc a b) p) p t :=
  (exists_diffeomorph_convexComb hn f.property t).choose_spec p

/-- At time `0` the straight-line contraction is the diffeomorphism itself. -/
@[simp]
theorem straightenIcc_zero (hn : n ≠ 0)
    (f : Diffeomorph.nhdsFixingSubgroup (I := 𝓡∂ 1) (n := n) ((𝓡∂ 1).boundary (Icc a b))) :
    straightenIcc hn f 0 = f :=
  Subtype.ext (Diffeomorph.ext fun p ↦ by rw [straightenIcc_apply, Icc.convexComb_zero])

/-- At time `1` the straight-line contraction is the identity. -/
@[simp]
theorem straightenIcc_one (hn : n ≠ 0)
    (f : Diffeomorph.nhdsFixingSubgroup (I := 𝓡∂ 1) (n := n) ((𝓡∂ 1).boundary (Icc a b))) :
    straightenIcc hn f 1 = 1 :=
  Subtype.ext (Diffeomorph.ext fun p ↦ by
    rw [straightenIcc_apply, Icc.convexComb_one, OneMemClass.coe_one, Diffeomorph.one_apply])

/-- The straight-line contraction fixes the identity at all times. -/
@[simp]
theorem straightenIcc_one_left (hn : n ≠ 0) (t : unitInterval) :
    straightenIcc (a := a) (b := b) hn 1 t = 1 :=
  Subtype.ext (Diffeomorph.ext fun p ↦ by
    rw [straightenIcc_apply, OneMemClass.coe_one, Diffeomorph.one_apply, Icc.convexComb_eq])

/-- **The straight-line contraction is smooth in the time parameter**: for a fixed `f`, the map
`(t, x) ↦ (1 - t) f x + t x` is jointly `C^n`. -/
theorem contMDiff_straightenIcc (hn : n ≠ 0)
    (f : Diffeomorph.nhdsFixingSubgroup (I := 𝓡∂ 1) (n := n) ((𝓡∂ 1).boundary (Icc a b))) :
    ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) (𝓡∂ 1) n fun q : unitInterval × Icc a b ↦
      (straightenIcc hn f q.1 : Icc a b ≃ₘ^n⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc a b) q.2 := by
  simp only [straightenIcc_apply]
  exact ContMDiff.convexComb ((f : Icc a b ≃ₘ^n⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc a b).contMDiff.comp contMDiff_snd)
    contMDiff_snd contMDiff_fst

/-- **The straight-line contraction is continuous** in the diffeomorphism and the time jointly,
for the weak Whitney topology. -/
theorem continuous_straightenIcc (hn : n ≠ 0) :
    Continuous fun q : Diffeomorph.nhdsFixingSubgroup (I := 𝓡∂ 1) (n := n)
        ((𝓡∂ 1).boundary (Icc a b)) × unitInterval ↦ straightenIcc hn q.1 q.2 := by
  have := ContMDiffMap.isTopologicalAddGroup_manifoldWeakWhitney (I := 𝓡∂ 1) (M := Icc a b)
    (F := ℝ) (n := n)
  have := (ContMDiffMap.withSeminorms_manifoldWeakWhitney (I := 𝓡∂ 1) (M := Icc a b)
    (F := ℝ) (n := n)).continuousSMul
  set ι : C^n⟮𝓡∂ 1, Icc a b; 𝓘(ℝ), ℝ⟯ := ContMDiffMap.subtypeValIcc
  have hemb := ContMDiffMap.isEmbedding_subtypeValIcc_comp (I := 𝓡∂ 1) (M := Icc a b) (n := n)
    (a := a) (b := b)
  refine continuous_induced_rng.mpr
    (Diffeomorph.continuous_weakWhitney_iff.mpr (hemb.continuous_iff.mpr ?_))
  have hf : Continuous fun q : Diffeomorph.nhdsFixingSubgroup (I := 𝓡∂ 1) (n := n)
      ((𝓡∂ 1).boundary (Icc a b)) × unitInterval ↦
      ι.comp (q.1 : Icc a b ≃ₘ^n⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc a b).toContMDiffMap :=
    hemb.continuous.comp
      (Diffeomorph.continuous_toContMDiffMap.comp (continuous_subtypeVal.comp continuous_fst))
  -- On real functions the contraction is the affine expression `x ↦ x + (1 - t) (f x - x)`.
  refine Continuous.congr (f := fun q ↦ ι + (1 - (q.2 : ℝ)) •
      (ι.comp (q.1 : Icc a b ≃ₘ^n⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc a b).toContMDiffMap - ι))
    (continuous_const.add (((continuous_const.sub
      (continuous_subtypeVal.comp continuous_snd)).smul (hf.sub continuous_const))))
    fun q ↦ ContMDiffMap.ext fun p ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, ContMDiffMap.comp_apply,
    Diffeomorph.coe_toContMDiffMap, straightenIcc_apply]
  simp only [ι, ContMDiffMap.coe_add, ContMDiffMap.coe_subtypeValIcc, ContMDiffMap.coe_smul,
    ContMDiffMap.coe_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, ContMDiffMap.comp_apply,
    Diffeomorph.coe_coe, smul_eq_mul, Icc.coe_convexComb]
  ring

variable (a b) in
/-- **The straight-line contraction as a homotopy.** It joins the identity map of the group of
diffeomorphisms of `[a, b]` equal to the identity near the endpoints to the constant map at the
identity diffeomorphism, and fixes the identity diffeomorphism throughout. -/
def straighteningHomotopyIcc (hn : n ≠ 0) :
    ContinuousMap.HomotopyRel
      (ContinuousMap.id (Diffeomorph.nhdsFixingSubgroup (I := 𝓡∂ 1) (n := n)
        ((𝓡∂ 1).boundary (Icc a b))))
      (ContinuousMap.const _ 1) {1} where
  toFun q := straightenIcc hn q.2 q.1
  continuous_toFun := (continuous_straightenIcc hn).comp continuous_swap
  map_zero_left := straightenIcc_zero hn
  map_one_left := straightenIcc_one hn
  prop' t f hf := by
    obtain rfl := mem_singleton_iff.mp hf
    exact straightenIcc_one_left hn t

/-- The straight-line homotopy at time `t` is the straight-line contraction at time `t`. -/
@[simp]
theorem straighteningHomotopyIcc_apply (hn : n ≠ 0) (t : unitInterval)
    (f : Diffeomorph.nhdsFixingSubgroup (I := 𝓡∂ 1) (n := n) ((𝓡∂ 1).boundary (Icc a b))) :
    straighteningHomotopyIcc a b hn (t, f) = straightenIcc hn f t :=
  (rfl)

variable (a b) in
/-- **Smale's theorem for the interval.** For `a < b` and `n ≠ 0`, the `C^n` diffeomorphisms of
`[a, b]` that are the identity on a neighbourhood of the endpoints form a contractible space in the
weak Whitney topology. -/
theorem contractibleSpace_nhdsFixingSubgroup_Icc (hn : n ≠ 0) :
    ContractibleSpace
      (Diffeomorph.nhdsFixingSubgroup (I := 𝓡∂ 1) (n := n) ((𝓡∂ 1).boundary (Icc a b))) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨1, ⟨(straighteningHomotopyIcc a b hn).toHomotopy⟩⟩

end TauCeti
