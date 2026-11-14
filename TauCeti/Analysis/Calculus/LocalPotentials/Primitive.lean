/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LocalPotentials.PathIntegral

import Mathlib.Analysis.Calculus.MeanValue

/-!
# Path-lifting primitives and the vanishing-loop-integral exactness criterion

For a covector field `φ : E → E →L[ℝ] F` with local potentials (`TauCeti.HasLocalPotentials`) on an
open set `s`, integrating `φ` along continuous paths in `s` from a base point `x₀` defines a
candidate global potential `TauCeti.localPotentialPrimitive s φ x₀`. Whenever `φ` has zero
`localPotentialCurveIntegral` along every continuous loop in `s` based at `x₀`, this candidate is
independent of the path from `x₀` and differentiates to `φ` throughout the path component of `x₀`
in `s`. Gluing across path components yields a domain-wide exactness criterion without assuming `s`
is connected or nonempty, nor assuming completeness of `F` or finite dimensionality of `E`.

## Main definitions

* `TauCeti.localPotentialPrimitive s φ x₀`: candidate global potential obtained by integrating `φ`
  from `x₀` along a path in `s` when one exists, and `0` outside the path component of `x₀` in `s`.

## Main results

* `HasLocalPotentials.localPotentialCurveIntegral_eq_of_forall_localPotentialCurveIntegral_eq_zero`
  -- vanishing of `localPotentialCurveIntegral` on loops at `x₀` implies path independence in the
  path component of `x₀` in `s`.
* `TauCeti.HasLocalPotentials.localPotentialPrimitive_eq`,
  `TauCeti.HasLocalPotentials.contDiffAt_localPotentialPrimitive`,
  `TauCeti.HasLocalPotentials.hasFDerivAt_localPotentialPrimitive`,
  `TauCeti.HasLocalPotentials.contDiffOn_localPotentialPrimitive`: path independence, `C¹`
  regularity, and Fréchet derivative of `localPotentialPrimitive`, alongside its `JoinedIn`
  characterization and linearity in `φ`.
* `HasLocalPotentials.exists_eq_hasFDerivAt_eqOn_of_forall_localPotentialCurveIntegral_eq_zero`:
  existence and uniqueness on `s` of a global `C¹` potential taking a prescribed value at `x₀`.
* `HasLocalPotentials.exists_hasFDerivAt_iff_forall_localPotentialCurveIntegral_eq_zero`,
  `HasLocalPotentials.exists_hasFDerivAt_iff_forall_localPotentialCurveIntegral_eq_zero_of_joinedIn`
  -- `φ` admits a global `C¹` potential on `s` if and only if its curve integral vanishes over every
  loop in `s` (or every loop based at `x₀` when `x₀` reaches every point of `s`).

## References

* Henri Cartan, *Elementary Theory of Analytic Functions of One or Several Complex Variables*,
  Chapter II, §§1, 3 (primitives constructed by path integration and the loop-vanishing criterion).
* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 4, §§1.3, 4.3 (line integrals depending
  only on endpoints and exact differentials on open sets).
-/

public section

open Filter Metric Set
open scoped ContDiff Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {a b x₀ : E} {s : Set E} {φ ψ : E → E →L[ℝ] F}

/-- If every loop in `s` based at `x₀` has zero curve integral, then any two paths in `s` sharing
endpoints in the path component of `x₀` in `s` have the same curve integral. -/
theorem
    HasLocalPotentials.localPotentialCurveIntegral_eq_of_forall_localPotentialCurveIntegral_eq_zero
    (hφ : HasLocalPotentials s φ)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0)
    (hjoin : JoinedIn s x₀ a) {p q : Path a b} (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    localPotentialCurveIntegral φ p = localPotentialCurveIntegral φ q := by
  let α : Path x₀ a := hjoin.somePath
  have hα : ∀ t, α t ∈ s := hjoin.somePath_mem
  have hps : ∀ t, (α.trans p) t ∈ s := fun t ↦ by
    rw [Path.trans_apply]; split_ifs <;> [exact hα _; exact hp _]
  have hqs : ∀ t, (α.trans q) t ∈ s := fun t ↦ by
    rw [Path.trans_apply]; split_ifs <;> [exact hα _; exact hq _]
  have hqs_symm : ∀ t, (α.trans q).symm t ∈ s := fun t ↦ hqs (unitInterval.symm t)
  let η : Path x₀ x₀ := (α.trans p).trans (α.trans q).symm
  have hη : localPotentialCurveIntegral φ η = 0 := hloop η fun t ↦ by
    rw [Path.trans_apply]; split_ifs <;> [exact hps _; exact hqs_symm _]
  rw [hφ.localPotentialCurveIntegral_trans hps hqs_symm, localPotentialCurveIntegral_symm,
    hφ.localPotentialCurveIntegral_trans hα hp,
    hφ.localPotentialCurveIntegral_trans hα hq] at hη
  calc
    localPotentialCurveIntegral φ p
      = ((localPotentialCurveIntegral φ α + localPotentialCurveIntegral φ p) +
          -(localPotentialCurveIntegral φ α + localPotentialCurveIntegral φ q)) +
        localPotentialCurveIntegral φ q := by abel
    _ = localPotentialCurveIntegral φ q := by rw [hη, zero_add]

/-- Candidate global potential of `φ` on `s` anchored at `x₀`, defined at `y` by integrating `φ`
along a path in `s` from `x₀` to `y` when one exists, and `0` otherwise. -/
noncomputable def localPotentialPrimitive (s : Set E) (φ : E → E →L[ℝ] F) (x₀ y : E) : F :=
  open Classical in
  if h : JoinedIn s x₀ y then localPotentialCurveIntegral φ h.somePath else 0

/-- Inside the path component of `x₀` in `s`, `localPotentialPrimitive` evaluates `φ` along the
chosen path `h.somePath`. -/
theorem localPotentialPrimitive_of_joinedIn {y : E} (h : JoinedIn s x₀ y) :
    localPotentialPrimitive s φ x₀ y = localPotentialCurveIntegral φ h.somePath := by
  rw [localPotentialPrimitive, dite_eq_left h]

/-- Outside the path component of `x₀` in `s`, `localPotentialPrimitive` returns `0`. -/
theorem localPotentialPrimitive_of_not_joinedIn {y : E} (h : ¬JoinedIn s x₀ y) :
    localPotentialPrimitive s φ x₀ y = 0 := by
  rw [localPotentialPrimitive, dite_eq_right h]

/-- On the empty domain, `localPotentialPrimitive` is identically zero. -/
@[simp]
theorem localPotentialPrimitive_empty (φ : E → E →L[ℝ] F) (x₀ y : E) :
    localPotentialPrimitive ∅ φ x₀ y = 0 :=
  localPotentialPrimitive_of_not_joinedIn fun ⟨_, hγ⟩ ↦ hγ 0

/-- The candidate primitive of the zero covector field is identically zero. -/
@[simp]
theorem localPotentialPrimitive_zero (s : Set E) (x₀ y : E) :
    localPotentialPrimitive s (0 : E → E →L[ℝ] F) x₀ y = 0 := by
  by_cases h : JoinedIn s x₀ y
  · rw [localPotentialPrimitive_of_joinedIn h, localPotentialCurveIntegral_zero]
  · exact localPotentialPrimitive_of_not_joinedIn h

/-- Negating the covector field negates `localPotentialPrimitive`. -/
@[simp]
theorem localPotentialPrimitive_neg (s : Set E) (φ : E → E →L[ℝ] F) (x₀ y : E) :
    localPotentialPrimitive s (-φ) x₀ y = -localPotentialPrimitive s φ x₀ y := by
  by_cases h : JoinedIn s x₀ y
  · rw [localPotentialPrimitive_of_joinedIn h, localPotentialPrimitive_of_joinedIn h,
      localPotentialCurveIntegral_neg]
  · rw [localPotentialPrimitive_of_not_joinedIn h, localPotentialPrimitive_of_not_joinedIn h,
      neg_zero]

/-- Scaling the covector field by a scalar in a division ring scales `localPotentialPrimitive`. -/
@[simp]
theorem localPotentialPrimitive_smul {R : Type*} [DivisionRing R] [Module R F]
    [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (s : Set E) (c : R) (φ : E → E →L[ℝ] F) (x₀ y : E) :
    localPotentialPrimitive s (c • φ) x₀ y = c • localPotentialPrimitive s φ x₀ y := by
  by_cases h : JoinedIn s x₀ y
  · rw [localPotentialPrimitive_of_joinedIn h, localPotentialPrimitive_of_joinedIn h,
      localPotentialCurveIntegral_smul]
  · rw [localPotentialPrimitive_of_not_joinedIn h, localPotentialPrimitive_of_not_joinedIn h,
      smul_zero]

/-- Two covector fields that agree on an open set `s` define the same `localPotentialPrimitive` on
`s`. -/
theorem localPotentialPrimitive_congr (hs : IsOpen s) (h : EqOn φ ψ s) (x₀ y : E) :
    localPotentialPrimitive s φ x₀ y = localPotentialPrimitive s ψ x₀ y := by
  by_cases hj : JoinedIn s x₀ y
  · rw [localPotentialPrimitive_of_joinedIn hj, localPotentialPrimitive_of_joinedIn hj]
    exact localPotentialCurveIntegral_congr hs h hj.somePath_mem
  · rw [localPotentialPrimitive_of_not_joinedIn hj, localPotentialPrimitive_of_not_joinedIn hj]

/-- If `φ` has local potentials on `s` and agrees with `ψ` on `s`, then `φ` and `ψ` have the same
`localPotentialPrimitive`. -/
theorem HasLocalPotentials.localPotentialPrimitive_congr (hφ : HasLocalPotentials s φ)
    (h : EqOn φ ψ s) (x₀ y : E) :
    localPotentialPrimitive s φ x₀ y = localPotentialPrimitive s ψ x₀ y :=
  TauCeti.localPotentialPrimitive_congr hφ.isOpen h x₀ y

/-- Adding two covector fields with local potentials on `s` adds their
`localPotentialPrimitive` values. -/
theorem HasLocalPotentials.localPotentialPrimitive_add (hφ : HasLocalPotentials s φ)
    (hψ : HasLocalPotentials s ψ) (x₀ y : E) :
    localPotentialPrimitive s (φ + ψ) x₀ y =
      localPotentialPrimitive s φ x₀ y + localPotentialPrimitive s ψ x₀ y := by
  by_cases hj : JoinedIn s x₀ y
  · rw [localPotentialPrimitive_of_joinedIn hj, localPotentialPrimitive_of_joinedIn hj,
      localPotentialPrimitive_of_joinedIn hj]
    exact hφ.localPotentialCurveIntegral_add hψ hj.somePath_mem
  · rw [localPotentialPrimitive_of_not_joinedIn hj, localPotentialPrimitive_of_not_joinedIn hj,
      localPotentialPrimitive_of_not_joinedIn hj, add_zero]

/-- Subtracting two covector fields with local potentials on `s` subtracts their
`localPotentialPrimitive` values. -/
theorem HasLocalPotentials.localPotentialPrimitive_sub (hφ : HasLocalPotentials s φ)
    (hψ : HasLocalPotentials s ψ) (x₀ y : E) :
    localPotentialPrimitive s (φ - ψ) x₀ y =
      localPotentialPrimitive s φ x₀ y - localPotentialPrimitive s ψ x₀ y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, hφ.localPotentialPrimitive_add hψ.neg,
    localPotentialPrimitive_neg]

/-- When loops at `x₀` in `s` have zero integral, `localPotentialPrimitive s φ x₀ y` equals the
integral along any path in `s` from `x₀` to `y`. -/
theorem HasLocalPotentials.localPotentialPrimitive_eq (hφ : HasLocalPotentials s φ)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0)
    {y : E} (γ : Path x₀ y) (hγ : ∀ t, γ t ∈ s) :
    localPotentialPrimitive s φ x₀ y = localPotentialCurveIntegral φ γ := by
  have hj : JoinedIn s x₀ y := ⟨γ, hγ⟩
  rw [localPotentialPrimitive_of_joinedIn hj]
  exact hφ.localPotentialCurveIntegral_eq_of_forall_localPotentialCurveIntegral_eq_zero hloop
    (JoinedIn.refl (γ.source ▸ hγ 0)) hj.somePath_mem hγ

/-- When loops at `x₀` in `s` have zero integral, `localPotentialPrimitive` vanishes at the base
point `x₀`. -/
theorem HasLocalPotentials.localPotentialPrimitive_self (hφ : HasLocalPotentials s φ)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0) :
    localPotentialPrimitive s φ x₀ x₀ = 0 := by
  by_cases hx₀ : x₀ ∈ s
  · rw [hφ.localPotentialPrimitive_eq hloop (Path.refl x₀) (fun _ ↦ hx₀),
      localPotentialCurveIntegral_refl]
  · exact localPotentialPrimitive_of_not_joinedIn fun h ↦ hx₀ h.source_mem

private theorem exists_eventuallyEq_localPotentialPrimitive (hφ : HasLocalPotentials s φ)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0)
    {z : E} (hjoin : JoinedIn s x₀ z) :
    ∃ g : E → F, ContDiffAt ℝ 1 g z ∧ HasFDerivAt g (φ z) z ∧
      localPotentialPrimitive s φ x₀ =ᶠ[𝓝 z] g := by
  obtain ⟨r, hr, hrs, gz, hgz, hdz⟩ := hasLocalPotentials_iff.mp hφ z hjoin.target_mem
  let α : Path x₀ z := hjoin.somePath
  have hα : ∀ t, α t ∈ s := hjoin.somePath_mem
  have heq : EqOn (localPotentialPrimitive s φ x₀)
      (fun y ↦ gz y + (localPotentialCurveIntegral φ α - gz z)) (ball z r) := by
    intro y hy
    have hseg_ball : ∀ t, (Path.segment z y) t ∈ ball z r := fun t ↦
      (convex_ball z r).segment_subset (mem_ball_self hr) hy
        (Path.range_segment z y ▸ mem_range_self t)
    have hseg_s : ∀ t, (Path.segment z y) t ∈ s := fun t ↦ hrs (hseg_ball t)
    have htrans_s : ∀ t, (α.trans (Path.segment z y)) t ∈ s := fun t ↦ by
      rw [Path.trans_apply]; split_ifs <;> [exact hα _; exact hseg_s _]
    dsimp only
    rw [hφ.localPotentialPrimitive_eq hloop (α.trans (Path.segment z y)) htrans_s,
      hφ.localPotentialCurveIntegral_trans hα hseg_s,
      localPotentialCurveIntegral_eq_sub_of_hasFDerivAt isOpen_ball hdz hseg_ball]
    abel
  refine ⟨fun y ↦ gz y + (localPotentialCurveIntegral φ α - gz z),
    (hgz.contDiffAt (ball_mem_nhds z hr)).add contDiffAt_const,
    by simpa only [add_zero] using
      (hdz z (mem_ball_self hr)).add_const (localPotentialCurveIntegral φ α - gz z),
    Filter.eventuallyEq_of_mem (ball_mem_nhds z hr) heq⟩

/-- At any point `z` joined to `x₀` in `s`, if all loops at `x₀` in `s` have zero integral, then
`localPotentialPrimitive s φ x₀` is `C¹` at `z`. -/
theorem HasLocalPotentials.contDiffAt_localPotentialPrimitive
    (hφ : HasLocalPotentials s φ)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0)
    {z : E} (hjoin : JoinedIn s x₀ z) :
    ContDiffAt ℝ 1 (localPotentialPrimitive s φ x₀) z := by
  obtain ⟨g, hc, -, hev⟩ := exists_eventuallyEq_localPotentialPrimitive hφ hloop hjoin
  exact hc.congr_of_eventuallyEq hev

/-- At any point `z` joined to `x₀` in `s`, if all loops at `x₀` in `s` have zero integral, then
`localPotentialPrimitive s φ x₀` has Fréchet derivative `φ z` at `z`. -/
theorem HasLocalPotentials.hasFDerivAt_localPotentialPrimitive
    (hφ : HasLocalPotentials s φ)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0)
    {z : E} (hjoin : JoinedIn s x₀ z) :
    HasFDerivAt (localPotentialPrimitive s φ x₀) (φ z) z := by
  obtain ⟨g, -, hd, hev⟩ := exists_eventuallyEq_localPotentialPrimitive hφ hloop hjoin
  exact hd.congr_of_eventuallyEq hev

/-- If `x₀` can be joined in `s` to every point of `s` and all loops in `s` based at `x₀` have zero
curve integral, then `localPotentialPrimitive s φ x₀` is `C¹` on `s`. -/
theorem HasLocalPotentials.contDiffOn_localPotentialPrimitive
    (hφ : HasLocalPotentials s φ) (hconn : ∀ y ∈ s, JoinedIn s x₀ y)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0) :
    ContDiffOn ℝ 1 (localPotentialPrimitive s φ x₀) s := fun w hw ↦
  (hφ.contDiffAt_localPotentialPrimitive hloop (hconn w hw)).contDiffWithinAt

/-- When `x₀ ∈ s` can be joined in `s` to every point of `s` and every loop in `s` based at `x₀`
has zero curve integral, `φ` admits a global `C¹` potential on `s` taking a prescribed value `y₀`
at `x₀`, unique on `s`. -/
theorem HasLocalPotentials.exists_eq_hasFDerivAt_eqOn_of_forall_localPotentialCurveIntegral_eq_zero
    (hφ : HasLocalPotentials s φ) (hx₀ : x₀ ∈ s) (hconn : ∀ y ∈ s, JoinedIn s x₀ y)
    (hloop : ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0) (y₀ : F) :
    ∃ g : E → F, ContDiffOn ℝ 1 g s ∧ g x₀ = y₀ ∧ (∀ w ∈ s, HasFDerivAt g (φ w) w) ∧
      ∀ g' : E → F, (∀ w ∈ s, HasFDerivAt g' (φ w) w) → g' x₀ = y₀ → EqOn g' g s := by
  have hs_conn : IsPathConnected s := ⟨x₀, hx₀, fun {y} hy ↦ hconn y hy⟩
  have hc := hφ.contDiffOn_localPotentialPrimitive hconn hloop
  have h0 := hφ.localPotentialPrimitive_self hloop
  have hd : ∀ w ∈ s,
      HasFDerivAt (fun z ↦ localPotentialPrimitive s φ x₀ z + y₀) (φ w) w := fun w hw ↦ by
    simpa only [add_zero] using
      (hφ.hasFDerivAt_localPotentialPrimitive hloop (hconn w hw)).add_const y₀
  refine ⟨fun w ↦ localPotentialPrimitive s φ x₀ w + y₀, hc.add contDiffOn_const, by simp [h0],
    hd, fun g' hd' hg'₀ ↦ ?_⟩
  exact hφ.isOpen.eqOn_of_fderiv_eq hs_conn.isConnected.isPreconnected
    (fun w hw ↦ (hd' w hw).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hd' w hw).fderiv.trans (hd w hw).fderiv.symm)
    hx₀ (by simp [hg'₀, h0])

/-- When `x₀` can be joined in `s` to every point of `s`, a covector field with local potentials on
`s` admits a global `C¹` potential if and only if its curve integral vanishes along every loop in
`s` based at `x₀`. -/
theorem
    HasLocalPotentials.exists_hasFDerivAt_iff_forall_localPotentialCurveIntegral_eq_zero_of_joinedIn
    (hφ : HasLocalPotentials s φ) (hconn : ∀ y ∈ s, JoinedIn s x₀ y) :
    (∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ w ∈ s, HasFDerivAt g (φ w) w) ↔
      ∀ η : Path x₀ x₀, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0 :=
  ⟨fun ⟨_, _, hd⟩ η hη ↦ by
      rw [localPotentialCurveIntegral_eq_sub_of_hasFDerivAt hφ.isOpen hd hη, sub_self],
    fun hloop ↦ ⟨localPotentialPrimitive s φ x₀,
      hφ.contDiffOn_localPotentialPrimitive hconn hloop,
      fun w hw ↦ hφ.hasFDerivAt_localPotentialPrimitive hloop (hconn w hw)⟩⟩

/-- A covector field with local potentials on `s` admits a global `C¹` potential on `s` if and only
if its curve integral vanishes along every loop in `s`. -/
theorem HasLocalPotentials.exists_hasFDerivAt_iff_forall_localPotentialCurveIntegral_eq_zero
    (hφ : HasLocalPotentials s φ) :
    (∃ g : E → F, ContDiffOn ℝ 1 g s ∧ ∀ w ∈ s, HasFDerivAt g (φ w) w) ↔
      ∀ x ∈ s, ∀ η : Path x x, (∀ t, η t ∈ s) → localPotentialCurveIntegral φ η = 0 := by
  refine ⟨fun ⟨_, _, hd⟩ _ _ η hη ↦ ?_, fun hloop ↦ ?_⟩
  · rw [localPotentialCurveIntegral_eq_sub_of_hasFDerivAt hφ.isOpen hd hη, sub_self]
  · let base : E → E := fun w ↦ Classical.epsilon fun x ↦ JoinedIn s x w
    let g : E → F := fun w ↦ localPotentialPrimitive s φ (base w) w
    have hev : ∀ z ∈ s, g =ᶠ[𝓝 z] localPotentialPrimitive s φ (base z) := by
      intro z hz
      obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hφ.isOpen z hz
      refine Filter.eventuallyEq_of_mem (ball_mem_nhds z hr) fun w hw ↦ ?_
      have hzw : JoinedIn s z w :=
        ⟨Path.segment z w, fun t ↦ hrs ((convex_ball z r).segment_subset
          (mem_ball_self hr) hw (Path.range_segment z w ▸ mem_range_self t))⟩
      have hbase_eq : base w = base z := by
        dsimp only [base]; congr 1; ext x
        exact ⟨fun hxw ↦ hxw.trans hzw.symm, fun hxz ↦ hxz.trans hzw⟩
      exact congrArg (fun b ↦ localPotentialPrimitive s φ b w) hbase_eq
    have hbase : ∀ z ∈ s, JoinedIn s (base z) z := fun z hz ↦
      Classical.epsilon_spec (p := fun x ↦ JoinedIn s x z) ⟨z, JoinedIn.refl hz⟩
    exact ⟨g, fun z hz ↦ ((hφ.contDiffAt_localPotentialPrimitive
        (hloop (base z) (hbase z hz).source_mem) (hbase z hz)).congr_of_eventuallyEq
        (hev z hz)).contDiffWithinAt,
      fun z hz ↦ (hφ.hasFDerivAt_localPotentialPrimitive
        (hloop (base z) (hbase z hz).source_mem) (hbase z hz)).congr_of_eventuallyEq (hev z hz)⟩

end TauCeti
