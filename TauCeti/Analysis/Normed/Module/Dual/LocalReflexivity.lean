/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Normed.Module.FinitelyRepresentable
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Analysis.Normed.Module.Annihilator
import TauCeti.Analysis.Normed.Module.Dual.Helly

/-!
# The principle of local reflexivity

The bidual `E**` of a normed space is in general much larger than `E`, but its
finite-dimensional pieces are not: every finite-dimensional subspace of `E**` maps back into `E`
almost isometrically. Precisely, let `ι : V → E**` be a linear isometry from a finite-dimensional
normed space, let `G` be a finite-dimensional subspace of the dual `E*`, and let `ε > 0`. Then
some linear map `T : V → E` satisfies `(1 - ε) ‖v‖ ≤ ‖T v‖ ≤ (1 + ε) ‖v‖`, preserves the pairing
with `G` (`g (T v) = ι v g` for `g ∈ G`), and inverts the canonical embedding `J : E → E**` on
`V` (`T v = x` whenever `ι v = J x`). This is the **principle of local reflexivity** of
Lindenstrauss and Rosenthal, a quantitative finite-dimensional form of Goldstine's theorem. In
particular `E**` is finitely representable in `E`.

## Main results

* `LinearIsometry.exists_continuousLinearMap_of_doubleDual`: the principle of local
  reflexivity, with the two-sided bounds `(1 - ε) ‖v‖ ≤ ‖T v‖ ≤ (1 + ε) ‖v‖`.
* `LinearIsometry.exists_continuousLinearMap_of_doubleDual_norm_le_mul`: the same with
  distortion at most `1 + ε`, in the form `‖T v‖ ≤ (1 + ε) ‖v‖` and `‖v‖ ≤ (1 + ε) ‖T v‖`.
* `TauCeti.finitelyRepresentable_doubleDual`: the bidual of a normed space is finitely
  representable in the space.

## Implementation notes

A finite-dimensional subspace `F` of `E**` enters through its inclusion `ι : F → E**`, as in
the proof of `TauCeti.finitelyRepresentable_doubleDual`; stating the theorem for an isometric
embedding of an arbitrary finite-dimensional normed space keeps it usable for maps that are not
literally inclusions.

Linear maps `T : V → E` are measured by their values
`(T uᵢ)ᵢ` at a finite net `uᵢ` of the unit sphere of `V`, in the sup-normed product `κ → E`.
Hahn–Banach and Helly's lemma (`StrongDual.exists_norm_lt_and_forall_apply_eq`) bound the
distance from a particular solution of the constraints to the subspace of corrections, which
gives `‖T uᵢ‖` close to one; extra functionals almost norming the net points give the lower
bound, and the net propagates both bounds to all of `V`.

## References

* J. Lindenstrauss and H. P. Rosenthal, *The `ℒ_p` spaces*, Israel J. Math. **7** (1969),
  325–349.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Theorem 12.2.4.
-/

public section

open Metric NormedSpace

variable {𝕜 E : Type*} [RCLike 𝕜]

namespace TauCeti

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A continuous functional annihilating the preannihilator of a finite-dimensional subspace `G`
of the dual lies in `G`: the continuous form of `Subspace.dualCoannihilator_dualAnnihilator_eq`. -/
private theorem mem_of_forall_apply_eq_zero {G : Submodule 𝕜 (StrongDual 𝕜 E)}
    [FiniteDimensional 𝕜 G] {ψ : StrongDual 𝕜 E}
    (hψ : ∀ e : E, (∀ g ∈ G, g e = 0) → ψ e = 0) : ψ ∈ G := by
  let W : Submodule 𝕜 (Module.Dual 𝕜 E) := G.map (ContinuousLinearMap.coeLM 𝕜)
  have hW : (ψ : Module.Dual 𝕜 E) ∈ W.dualCoannihilator.dualAnnihilator := by
    simp only [Submodule.mem_dualAnnihilator, Submodule.mem_dualCoannihilator]
    intro e he
    exact hψ e fun g hg ↦ he g (Submodule.mem_map_of_mem hg)
  rw [Subspace.dualCoannihilator_dualAnnihilator_eq] at hW
  obtain ⟨g, hg, hgψ⟩ := hW
  rwa [← ContinuousLinearMap.coe_injective hgψ]

variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]

/-- The finite-system core of local reflexivity. Let `ι : V → E**` be linear on a
finite-dimensional space, let `G ≤ E*` be finite-dimensional, let `A` lift `ι` into `E` on a
subspace `F₀`, and let `uᵢ` be finitely many points of `V` with `‖ι uᵢ‖ ≤ 1`. Then for every
`δ > 0` some linear map `T : V → E` extends `A`, satisfies `g (T v) = ι v g` for `g ∈ G`, and
satisfies `‖T uᵢ‖ < 1 + δ`. -/
private theorem exists_linearMap_norm_apply_lt
    (ι : V →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E))
    (G : Submodule 𝕜 (StrongDual 𝕜 E)) [FiniteDimensional 𝕜 G]
    (F₀ : Submodule 𝕜 V) (A : F₀ →ₗ[𝕜] E)
    (hA : ∀ φ : F₀, inclusionInDoubleDual 𝕜 E (A φ) = ι φ)
    {κ : Type*} [Finite κ] (u : κ → V) (hu : ∀ i, ‖ι (u i)‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : V →ₗ[𝕜] E, (∀ φ : F₀, T φ = A φ) ∧ (∀ v, ∀ g ∈ G, g (T v) = ι v g) ∧
      ∀ i, ‖T (u i)‖ < 1 + δ := by
  classical
  cases nonempty_fintype κ
  -- A particular solution: `A` on `F₀`, and Helly solutions on a basis of a complement `F₁`.
  obtain ⟨F₁, hF⟩ := Submodule.exists_isCompl F₀
  let b := Module.finBasis 𝕜 F₁
  have hx : ∀ j, ∃ x : E, ∀ g ∈ G, g x = ι (b j) g := by
    intro j
    obtain ⟨x, -, hx⟩ := StrongDual.exists_norm_lt_and_forall_mem_apply_eq (ι (b j)) G one_pos
    exact ⟨x, hx⟩
  choose x hx using hx
  let T₀ : V →ₗ[𝕜] E := LinearMap.ofIsCompl hF A (b.constr 𝕜 x)
  let p := F₀.projectionOnto F₁ hF
  let q := F₁.projectionOnto F₀ hF.symm
  have hpq : ∀ v, ((p v : F₀) : V) + ((q v : F₁) : V) = v := fun v ↦ by
    simpa [p, q] using LinearMap.congr_fun (Submodule.subtype_comp_projectionOnto_add_eq_id hF) v
  -- The defect of `T₀` against a functional `h` is linear, vanishes on `F₀`, and is computed on
  -- the basis of `F₁`.
  let d : StrongDual 𝕜 E → V →ₗ[𝕜] 𝕜 := fun h ↦
    (ContinuousLinearMap.apply 𝕜 𝕜 h : StrongDual 𝕜 (StrongDual 𝕜 E) →ₗ[𝕜] 𝕜) ∘ₗ ι -
      (h : E →ₗ[𝕜] 𝕜) ∘ₗ T₀
  have hd : ∀ h v, d h v = ∑ j, b.repr (q v) j * (ι (b j) h - h (x j)) := by
    intro h v
    have h₀ : d h (p v : V) = 0 := by
      simp [d, T₀, ← hA, dual_def]
    have h₁ : ∀ ψ : F₁, d h (ψ : V) = ∑ j, b.repr ψ j * (ι (b j) h - h (x j)) := by
      intro ψ
      have hψ : (ψ : V) = ∑ j, b.repr ψ j • (b j : V) := by
        conv_lhs => rw [← b.sum_repr ψ]
        simp only [Submodule.coe_sum, Submodule.coe_smul]
      rw [hψ, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp [d, T₀]
    have := congrArg (d h) (hpq v)
    rw [map_add, h₀, zero_add, h₁] at this
    exact this.symm
  have hT₀ : ∀ v, ∀ g ∈ G, g (T₀ v) = ι v g := by
    intro v g hg
    have := hd g v
    simp only [hx _ g hg, sub_self, mul_zero, Finset.sum_const_zero] at this
    exact (by simpa [d, sub_eq_zero] using this : ι v g = g (T₀ v)).symm
  -- Measure a linear map by its values at the points `u i`.
  let N : (V →ₗ[𝕜] E) →ₗ[𝕜] κ → E := LinearMap.pi fun i ↦ LinearMap.applyₗ (u i)
  have hN : ∀ S i, N S i = S (u i) := fun _ _ ↦ rfl
  -- The corrections: linear maps vanishing on `F₀` with values in the preannihilator of `G`.
  let K : Submodule 𝕜 (V →ₗ[𝕜] E) :=
    { carrier := {S | (∀ φ : F₀, S φ = 0) ∧ ∀ v, ∀ g ∈ G, g (S v) = 0}
      add_mem' := fun {S S'} hS hS' ↦
        ⟨fun φ ↦ by simp [hS.1 φ, hS'.1 φ], fun v g hg ↦ by simp [hS.2 v g hg, hS'.2 v g hg]⟩
      zero_mem' := ⟨fun _ ↦ rfl, fun _ _ _ ↦ by simp⟩
      smul_mem' := fun c S hS ↦
        ⟨fun φ ↦ by simp [hS.1 φ], fun v g hg ↦ by simp [hS.2 v g hg]⟩ }
  let W := K.map N
  -- A Hahn–Banach functional attaining the distance from `N T₀` to `W`.
  obtain ⟨f, hfW, hf1, hfT⟩ := Submodule.exists_dual_eq_infDist W (N T₀)
  let h : κ → StrongDual 𝕜 E := fun i ↦ f.comp (ContinuousLinearMap.single 𝕜 (fun _ ↦ E) i)
  have hf : ∀ z : κ → E, f z = ∑ i, h i (z i) := by
    intro z
    conv_lhs => rw [← Finset.univ_sum_single z]
    simp [h, map_sum]
  -- The functional acts on the corrections only through `G`.
  have hψ : ∀ j, ∑ i, b.repr (q (u i)) j • h i ∈ G := by
    intro j
    refine mem_of_forall_apply_eq_zero fun e he ↦ ?_
    let S : V →ₗ[𝕜] E := ((b.coord j : F₁ →ₗ[𝕜] 𝕜) ∘ₗ q).smulRight e
    have hS : S ∈ K := by
      refine ⟨fun φ ↦ ?_, fun v g hg ↦ ?_⟩
      · simp [S, q, Submodule.projectionOnto_apply_right]
      · simp [S, he g hg]
    have := hfW (N S) (Submodule.mem_map_of_mem hS)
    rw [hf] at this
    simpa [S, hN, mul_comm] using this
  -- Hence `f (N T₀)` is the value of the bidual vector `(ι (u i))ᵢ` at `f`.
  have hfu : f (N T₀) = ∑ i, ι (u i) (h i) := by
    have hsum : ∑ i, d (h i) (u i) = 0 := by
      simp_rw [hd]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      have hj := hx j _ (hψ j)
      simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, smul_eq_mul] at hj
      simp [mul_sub, Finset.sum_sub_distrib, hj]
    have : ∑ i, ι (u i) (h i) - ∑ i, h i (T₀ (u i)) = 0 := by
      simpa [d, Finset.sum_sub_distrib] using hsum
    rw [hf]
    exact (sub_eq_zero.1 this).symm
  -- Helly's lemma, coordinatewise, bounds this value by one.
  have hle : infDist (N T₀) (W : Set (κ → E)) ≤ 1 := by
    refine le_of_forall_pos_le_add fun η hη ↦ ?_
    have he : ∀ i, ∃ e : E, ‖e‖ < 1 + η ∧ h i e = ι (u i) (h i) := by
      intro i
      obtain ⟨e, he, hhe⟩ := StrongDual.exists_norm_lt_and_forall_apply_eq
        (ι (u i)) (fun _ : Unit ↦ h i) hη
      exact ⟨e, he.trans_le (by simpa using hu i), hhe ()⟩
    choose e he hhe using he
    have hfe : f e = f (N T₀) := by rw [hfu, hf]; simp [hhe]
    have : ‖f (N T₀)‖ ≤ 1 + η := by
      rw [← hfe]
      calc ‖f e‖ ≤ ‖f‖ * ‖e‖ := f.le_opNorm e
        _ ≤ 1 * (1 + η) := by
          gcongr
          exact (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ (he i).le
        _ = 1 + η := one_mul _
    rwa [hfT, RCLike.norm_ofReal, abs_of_nonneg infDist_nonneg] at this
  -- Correct `T₀` by a nearly closest correction.
  obtain ⟨w, hwW, hw⟩ :=
    (infDist_lt_iff ⟨0, W.zero_mem⟩).1 (hle.trans_lt (lt_add_of_pos_right 1 hδ))
  obtain ⟨S, hSK, rfl⟩ := hwW
  refine ⟨T₀ - S, fun φ ↦ ?_, fun v g hg ↦ ?_, fun i ↦ ?_⟩
  · simp [hSK.1 φ, T₀]
  · simp [hSK.2 v g hg, hT₀ v g hg]
  · rw [dist_eq_norm] at hw
    calc ‖(T₀ - S) (u i)‖ = ‖(N T₀ - N S) i‖ := by simp [hN]
      _ ≤ ‖N T₀ - N S‖ := norm_le_pi_norm _ i
      _ < 1 + δ := hw

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Two-sided bounds `1 - δ < ‖T v‖ < 1 + δ` on a `δ`-net of the unit sphere, for `δ ≤ 1 / 6`,
give `(1 - 3 δ) ‖v‖ ≤ ‖T v‖ ≤ (1 + 3 δ) ‖v‖` everywhere. -/
private theorem norm_apply_bounds_of_net {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : V →L[𝕜] F) {t : Set V} {δ : ℝ} (hnear : ∀ w : V, ‖w‖ = 1 → ∃ v ∈ t, ‖w - v‖ < δ)
    (hlow : ∀ v ∈ t, 1 - δ < ‖T v‖) (hup : ∀ v ∈ t, ‖T v‖ < 1 + δ) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 6) :
    (∀ v, (1 - 3 * δ) * ‖v‖ ≤ ‖T v‖) ∧ ∀ v, ‖T v‖ ≤ (1 + 3 * δ) * ‖v‖ := by
  -- Propagate the upper bound to the unit sphere, and then bound `‖T‖`.
  have hTnorm : ‖T‖ ≤ 1 + 3 * δ := by
    have hbound : ‖T‖ ≤ 1 + δ + ‖T‖ * δ := by
      refine T.opNorm_le_of_unit_norm (by positivity) fun w hw ↦ ?_
      obtain ⟨v, hv, hwv⟩ := hnear w hw
      calc ‖T w‖ = ‖T v + T (w - v)‖ := by rw [map_sub, add_sub_cancel]
        _ ≤ ‖T v‖ + ‖T (w - v)‖ := norm_add_le _ _
        _ ≤ (1 + δ) + ‖T‖ * δ := by
          gcongr
          · exact (hup v hv).le
          · exact (T.le_opNorm _).trans (by gcongr)
    nlinarith [norm_nonneg T]
  -- The lower bound on the unit sphere.
  have hsphere : ∀ w : V, ‖w‖ = 1 → 1 - 3 * δ ≤ ‖T w‖ := by
    intro w hw
    obtain ⟨v, hv, hwv⟩ := hnear w hw
    have hTwv : ‖T (w - v)‖ ≤ (1 + 3 * δ) * δ :=
      (T.le_opNorm _).trans (mul_le_mul hTnorm hwv.le (norm_nonneg _) (by positivity))
    have : ‖T v‖ ≤ ‖T w‖ + ‖T (w - v)‖ := by
      calc ‖T v‖ = ‖T w - T (w - v)‖ := by rw [map_sub, sub_sub_cancel]
        _ ≤ ‖T w‖ + ‖T (w - v)‖ := norm_sub_le _ _
    nlinarith [hlow v hv]
  refine ⟨fun v ↦ ?_, fun v ↦ (T.le_opNorm v).trans (by gcongr)⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hTv : ‖T v‖ = ‖v‖ * ‖T ((‖v‖⁻¹ : 𝕜) • v)‖ := by
    rw [map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm,
      mul_inv_cancel_left₀ (norm_ne_zero_iff.2 hv)]
  rw [hTv, mul_comm]
  exact mul_le_mul_of_nonneg_left (hsphere _ (norm_smul_inv_norm hv)) (norm_nonneg v)

end Normed

end TauCeti

namespace LinearIsometry

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **The principle of local reflexivity.** Let `ι : V → E**` be a linear isometry from a
finite-dimensional normed space into the bidual of `E`, let `G` be a finite-dimensional subspace
of the dual of `E`, and let `ε > 0`. Then some continuous linear map `T : V → E` satisfies
`(1 - ε) ‖v‖ ≤ ‖T v‖ ≤ (1 + ε) ‖v‖`, preserves the pairing with `G` in the sense that
`g (T v) = ι v g` for `g ∈ G`, and inverts the canonical embedding on `V`: `T v = x` whenever
`ι v` is the canonical image of `x : E`. -/
theorem exists_continuousLinearMap_of_doubleDual [FiniteDimensional 𝕜 V]
    (ι : V →ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E))
    (G : Submodule 𝕜 (StrongDual 𝕜 E)) [FiniteDimensional 𝕜 G] {ε : ℝ} (hε : 0 < ε) :
    ∃ T : V →L[𝕜] E, (∀ v, (1 - ε) * ‖v‖ ≤ ‖T v‖ ∧ ‖T v‖ ≤ (1 + ε) * ‖v‖) ∧
      (∀ v, ∀ g ∈ G, g (T v) = ι v g) ∧
      ∀ v x, ι v = inclusionInDoubleDual 𝕜 E x → T v = x := by
  classical
  have := FiniteDimensional.proper_rclike 𝕜 V
  set δ := min ε 1 / 6 with hδ_def
  have hδ : 0 < δ := by positivity
  have hδε : 3 * δ ≤ ε := by
    have := min_le_left ε 1
    rw [hδ_def]; linarith
  have hδ1 : δ ≤ 1 / 6 := by
    have := min_le_right ε 1
    rw [hδ_def]; linarith
  -- A finite `δ`-net `t` of the unit sphere of `V`.
  obtain ⟨t, hts, htf, hcover⟩ := finite_cover_balls_of_compact (isCompact_sphere (0 : V) 1) hδ
  have := htf.to_subtype
  have hnorm : ∀ v : t, ‖(v : V)‖ = 1 := fun v ↦ mem_sphere_zero_iff_norm.1 (hts v.2)
  -- Functionals of norm less than one almost norming the net points.
  have hnorming : ∀ v : t, ∃ h : StrongDual 𝕜 E, ‖h‖ < 1 ∧ 1 - δ < ‖ι v h‖ := fun v ↦
    (ι v).exists_lt_apply_of_lt_opNorm (by rw [ι.norm_map, hnorm v]; linarith)
  choose h hh1 hh using hnorming
  let G' := G ⊔ Submodule.span 𝕜 (Set.range h)
  have : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range h)) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range h)
  have : FiniteDimensional 𝕜 G' := Submodule.finiteDimensional_sup _ _
  -- The lift of `ι` into `E` on the part of `V` mapped into the canonical image of `E`.
  let J := inclusionInDoubleDual 𝕜 E
  have hJ : Function.Injective J := (inclusionInDoubleDualLi 𝕜 (E := E)).injective
  let F₀ : Submodule 𝕜 V := (LinearMap.range (J : E →ₗ[𝕜] _)).comap ι.toLinearMap
  let A : F₀ →ₗ[𝕜] E :=
    LinearMap.codRestrictOfInjective (ι.toLinearMap ∘ₗ F₀.subtype) J hJ fun φ ↦ φ.2
  have hA : ∀ φ : F₀, J (A φ) = ι φ := fun φ ↦
    LinearMap.codRestrictOfInjective_comp_apply (ι.toLinearMap ∘ₗ F₀.subtype) (J : E →ₗ[𝕜] _)
      hJ _ φ
  obtain ⟨T', hTA, hTG, hTu⟩ := TauCeti.exists_linearMap_norm_apply_lt ι.toLinearMap G' F₀ A hA
    (fun v : t ↦ (v : V))
    (fun v ↦ le_of_eq (by rw [LinearIsometry.coe_toLinearMap, ι.norm_map, hnorm v])) hδ
  let T : V →L[𝕜] E := LinearMap.toContinuousLinearMap T'
  have hT : ∀ v, T v = T' v := fun _ ↦ rfl
  -- Every unit vector is within `δ` of a net point.
  have hnear : ∀ w : V, ‖w‖ = 1 → ∃ v ∈ t, ‖w - v‖ < δ := by
    intro w hw
    obtain ⟨v, hv, hwv⟩ := Set.mem_iUnion₂.1 (hcover (mem_sphere_zero_iff_norm.2 hw))
    exact ⟨v, hv, by rwa [mem_ball, dist_eq_norm] at hwv⟩
  -- The bounds at the net points.
  have hlow : ∀ v ∈ t, 1 - δ < ‖T v‖ := by
    intro v hv
    have hmem : h ⟨v, hv⟩ ∈ G' := Submodule.mem_sup_right (Submodule.subset_span ⟨_, rfl⟩)
    calc 1 - δ < ‖ι v (h ⟨v, hv⟩)‖ := hh ⟨v, hv⟩
      _ = ‖h ⟨v, hv⟩ (T v)‖ := by rw [hT, hTG v _ hmem, LinearIsometry.coe_toLinearMap]
      _ ≤ ‖h ⟨v, hv⟩‖ * ‖T v‖ := (h _).le_opNorm _
      _ ≤ 1 * ‖T v‖ := by gcongr; exact (hh1 _).le
      _ = ‖T v‖ := one_mul _
  obtain ⟨hTlow, hTup⟩ := TauCeti.norm_apply_bounds_of_net T hnear hlow
    (fun v hv ↦ by simpa [hT] using hTu ⟨v, hv⟩) hδ.le hδ1
  refine ⟨T, fun v ↦ ⟨?_, ?_⟩, fun v g hg ↦ hTG v g (Submodule.mem_sup_left hg), ?_⟩
  · exact (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg v)).trans (hTlow v)
  · exact (hTup v).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg v))
  · intro v x hv
    have hmem : v ∈ F₀ := ⟨x, hv.symm⟩
    apply hJ
    rw [hT, ← hv, hTA ⟨v, hmem⟩, hA]

/-- **The principle of local reflexivity**, with distortion at most `1 + ε`: under the
hypotheses of `LinearIsometry.exists_continuousLinearMap_of_doubleDual`, some continuous linear
map `T : V → E` satisfies `‖T v‖ ≤ (1 + ε) ‖v‖` and `‖v‖ ≤ (1 + ε) ‖T v‖`, preserves the pairing
with `G` and inverts the canonical embedding on `V`. -/
theorem exists_continuousLinearMap_of_doubleDual_norm_le_mul [FiniteDimensional 𝕜 V]
    (ι : V →ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)) (G : Submodule 𝕜 (StrongDual 𝕜 E))
    [FiniteDimensional 𝕜 G] {ε : ℝ} (hε : 0 < ε) :
    ∃ T : V →L[𝕜] E, (∀ v, ‖T v‖ ≤ (1 + ε) * ‖v‖ ∧ ‖v‖ ≤ (1 + ε) * ‖T v‖) ∧
      (∀ v, ∀ g ∈ G, g (T v) = ι v g) ∧
      ∀ v x, ι v = inclusionInDoubleDual 𝕜 E x → T v = x := by
  obtain ⟨T, hT, hTG, hTJ⟩ :=
    ι.exists_continuousLinearMap_of_doubleDual G (ε := ε / (1 + ε)) (by positivity)
  refine ⟨T, fun v ↦ ⟨(hT v).2.trans ?_, ?_⟩, hTG, hTJ⟩
  · gcongr
    exact div_le_self hε.le (by linarith)
  · have h1 : (1 + ε) * (1 - ε / (1 + ε)) = 1 := by field_simp; ring
    calc ‖v‖ = (1 + ε) * ((1 - ε / (1 + ε)) * ‖v‖) := by rw [← mul_assoc, h1, one_mul]
      _ ≤ (1 + ε) * ‖T v‖ := by gcongr; exact (hT v).1

end LinearIsometry

namespace TauCeti

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The bidual of a normed space is finitely representable in the space. -/
theorem finitelyRepresentable_doubleDual :
    FinitelyRepresentable 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) E :=
  finitelyRepresentable_iff.2 fun S _ ε hε ↦ by
    -- The inclusion of `S`, elaborated against the norm structure of the main theorem.
    obtain ⟨T, hT, -, -⟩ := LinearIsometry.exists_continuousLinearMap_of_doubleDual
      (𝕜 := 𝕜) (E := E) (V := S)
      { toFun := fun v ↦ (v : StrongDual 𝕜 (StrongDual 𝕜 E))
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        norm_map' := fun _ ↦ rfl } ⊥ hε
    exact ⟨T, hT⟩

end TauCeti
