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
import TauCeti.Analysis.Normed.Module.Annihilator
import TauCeti.Analysis.Normed.Module.Dual.Helly
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.LinearAlgebra.Projection

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
* `LinearIsometry.exists_continuousLinearMap_of_doubleDual_norm_le_mul`: the same with the
  bounds `‖T v‖ ≤ (1 + ε) ‖v‖` and `‖v‖ ≤ (1 + ε) ‖T v‖`.
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
bound, and the net propagates both bounds to all of `V`
(`ContinuousLinearMap.norm_apply_bounds_of_net`).

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

variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- A functional `f` on `κ → E` that vanishes at the values `(S uᵢ)ᵢ` of every correction `S`
(a linear map vanishing on `F₀` with values in the preannihilator of `G`) acts on corrections
only through `G`: for each vector of a basis of a complement `F₁` of `F₀`, the matching
combination of the coordinate functionals of `f` lies in `G`. -/
private theorem sum_repr_smul_comp_single_mem
    (G : Submodule 𝕜 (StrongDual 𝕜 E)) [FiniteDimensional 𝕜 G] {F₀ F₁ : Submodule 𝕜 V}
    (hF : IsCompl F₀ F₁) {ι' : Type*} (b : Module.Basis ι' 𝕜 F₁)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (u : κ → V) (f : StrongDual 𝕜 (κ → E))
    (hf : ∀ S : V →ₗ[𝕜] E, (∀ φ : F₀, S φ = 0) → (∀ v, ∀ g ∈ G, g (S v) = 0) →
      f (fun i ↦ S (u i)) = 0) (j : ι') :
    ∑ i, b.repr (F₁.projectionOnto F₀ hF.symm (u i)) j • f.comp (.single 𝕜 (fun _ ↦ E) i) ∈
      G := by
  rw [← Submodule.orthogonalBilin_orthogonalBilin_topDualPairing_flip_eq_of_finiteDimensional G]
  simp only [Submodule.mem_orthogonalBilin, LinearMap.flip_apply, topDualPairing_apply]
  intro e he
  let S : V →ₗ[𝕜] E := ((b.coord j : F₁ →ₗ[𝕜] 𝕜) ∘ₗ F₁.projectionOnto F₀ hF.symm).smulRight e
  have := hf S (fun φ ↦ by simp [S, Submodule.projectionOnto_apply_right])
    fun v g hg ↦ by simp [S, he g hg]
  rw [← ContinuousLinearMap.sum_comp_single (L := f)] at this
  simpa [S, mul_comm] using this

variable [FiniteDimensional 𝕜 V]

/-- A particular solution of the constraints of local reflexivity: a linear map `T₀ : V → E`
that extends a lift `A` of `ι` on `F₀` and preserves the pairing with a finite-dimensional
`G ≤ E*`. -/
private theorem exists_linearMap_extend_apply_eq
    (ι : V →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E))
    (G : Submodule 𝕜 (StrongDual 𝕜 E)) [FiniteDimensional 𝕜 G]
    (F₀ : Submodule 𝕜 V) (A : F₀ →ₗ[𝕜] E)
    (hA : ∀ φ : F₀, inclusionInDoubleDual 𝕜 E (A φ) = ι φ) :
    ∃ T₀ : V →ₗ[𝕜] E, (∀ φ : F₀, T₀ φ = A φ) ∧ ∀ v, ∀ g ∈ G, g (T₀ v) = ι v g := by
  -- `A` on `F₀`, and Helly solutions on a basis of a complement `F₁`.
  obtain ⟨F₁, hF⟩ := Submodule.exists_isCompl F₀
  let b := Module.finBasis 𝕜 F₁
  have hx : ∀ j, ∃ x : E, ∀ g ∈ G, g x = ι (b j) g := by
    intro j
    obtain ⟨x, -, hx⟩ := StrongDual.exists_norm_lt_and_forall_mem_apply_eq (ι (b j)) G one_pos
    exact ⟨x, hx⟩
  choose x hx using hx
  refine ⟨LinearMap.ofIsCompl hF A (b.constr 𝕜 x), fun φ ↦ LinearMap.ofIsCompl_apply_left hF φ,
    fun v g hg ↦ ?_⟩
  have h₁ : (g : E →ₗ[𝕜] 𝕜) ∘ₗ b.constr 𝕜 x =
      (ContinuousLinearMap.apply 𝕜 𝕜 g : StrongDual 𝕜 (StrongDual 𝕜 E) →ₗ[𝕜] 𝕜) ∘ₗ ι ∘ₗ
        F₁.subtype :=
    b.ext fun j ↦ by simp [hx j g hg]
  obtain ⟨y, hy, z, hz, rfl⟩ :=
    Submodule.mem_sup.1 (hF.sup_eq_top ▸ Submodule.mem_top : v ∈ F₀ ⊔ F₁)
  have hy' := LinearMap.ofIsCompl_apply_left hF (φ := A) (ψ := b.constr 𝕜 x) ⟨y, hy⟩
  have hz' := LinearMap.ofIsCompl_apply_right hF (φ := A) (ψ := b.constr 𝕜 x) ⟨z, hz⟩
  have hgz := LinearMap.congr_fun h₁ ⟨z, hz⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
    Submodule.coe_subtype, ContinuousLinearMap.apply_apply] at hgz hy' hz'
  have hAy : inclusionInDoubleDual 𝕜 E (A ⟨y, hy⟩) = ι y := hA ⟨y, hy⟩
  simp only [map_add, add_apply, hy', hz', hgz, ← hAy, dual_def]

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
  obtain ⟨T₀, hT₀A, hT₀⟩ := exists_linearMap_extend_apply_eq ι G F₀ A hA
  obtain ⟨F₁, hF⟩ := Submodule.exists_isCompl F₀
  let b := Module.finBasis 𝕜 F₁
  let q := F₁.projectionOnto F₀ hF.symm
  -- The defect of `T₀` against a functional `h` vanishes on `F₀`, so it is computed on the basis
  -- of `F₁`.
  let d : StrongDual 𝕜 E → V →ₗ[𝕜] 𝕜 := fun h ↦
    (ContinuousLinearMap.apply 𝕜 𝕜 h : StrongDual 𝕜 (StrongDual 𝕜 E) →ₗ[𝕜] 𝕜) ∘ₗ ι -
      (h : E →ₗ[𝕜] 𝕜) ∘ₗ T₀
  have hd : ∀ h v, d h v = ∑ j, b.repr (q v) j * (ι (b j) h - h (T₀ (b j))) := by
    intro h v
    rw [Submodule.apply_eq_sum_repr_projectionOnto hF b (d h)
      (fun φ ↦ by simp [d, hT₀A, ← hA, dual_def]) v]
    simp [d, q]
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
  have hf : ∀ z : κ → E, f z = ∑ i, h i (z i) := fun z ↦
    (ContinuousLinearMap.sum_comp_single (L := f) (v := z)).symm
  -- The functional acts on the corrections only through `G`.
  have hψ : ∀ j, ∑ i, b.repr (q (u i)) j • h i ∈ G :=
    sum_repr_smul_comp_single_mem G hF b u f fun S hS₀ hSG ↦
      hfW (N S) (Submodule.mem_map_of_mem ⟨hS₀, hSG⟩)
  -- Hence `f (N T₀)` is the value of the bidual vector `(ι (u i))ᵢ` at `f`.
  have hfu : f (N T₀) = ∑ i, ι (u i) (h i) := by
    have hsum : ∑ i, d (h i) (u i) = 0 := by
      simp_rw [hd]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      have hj := hT₀ (b j) _ (hψ j)
      simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, smul_eq_mul] at hj
      simp [mul_sub, Finset.sum_sub_distrib, hj]
    have : ∑ i, ι (u i) (h i) - ∑ i, h i (T₀ (u i)) = 0 := by
      simpa [d, Finset.sum_sub_distrib] using hsum
    rw [hf]
    exact (sub_eq_zero.1 this).symm
  -- Helly's lemma, coordinatewise, bounds this value by one.
  have hle : infDist (N T₀) (W : Set (κ → E)) ≤ 1 := by
    have := StrongDual.norm_sum_apply_comp_single_le f hf1 (fun i ↦ ι (u i)) hu
    -- Fold the coordinate functionals `f.comp (single i)` into their local name `h i`.
    change ‖∑ i, ι (u i) (h i)‖ ≤ 1 at this
    rwa [← hfu, hfT, RCLike.norm_ofReal, abs_of_nonneg infDist_nonneg] at this
  -- Correct `T₀` by a nearly closest correction.
  obtain ⟨w, hwW, hw⟩ :=
    (infDist_lt_iff ⟨0, W.zero_mem⟩).1 (hle.trans_lt (lt_add_of_pos_right 1 hδ))
  obtain ⟨S, hSK, rfl⟩ := hwW
  refine ⟨T₀ - S, fun φ ↦ ?_, fun v g hg ↦ ?_, fun i ↦ ?_⟩
  · simp [hSK.1 φ, hT₀A]
  · simp [hSK.2 v g hg, hT₀ v g hg]
  · rw [dist_eq_norm] at hw
    calc ‖(T₀ - S) (u i)‖ = ‖(N T₀ - N S) i‖ := by simp [hN]
      _ ≤ ‖N T₀ - N S‖ := norm_le_pi_norm _ i
      _ < 1 + δ := hw

end Seminormed

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
  have hT : ∀ v, T v = T' v := fun v ↦ by simp [T]
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
  obtain ⟨hTlow, hTup⟩ := T.norm_apply_bounds_of_net hnear hlow
    (fun v hv ↦ by simpa [hT] using hTu ⟨v, hv⟩) hδ.le hδ1
  refine ⟨T, fun v ↦ ⟨?_, ?_⟩, fun v g hg ↦ hTG v g (Submodule.mem_sup_left hg), ?_⟩
  · exact (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg v)).trans (hTlow v)
  · exact (hTup v).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg v))
  · intro v x hv
    have hmem : v ∈ F₀ := ⟨x, hv.symm⟩
    apply hJ
    rw [hT, ← hv, hTA ⟨v, hmem⟩, hA]

/-- **The principle of local reflexivity**, with multiplicative bounds: under the
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
    obtain ⟨T, hT, -, -⟩ := LinearIsometry.exists_continuousLinearMap_of_doubleDual
      (𝕜 := 𝕜) (E := E) (V := S) S.subtypeₗᵢ ⊥ hε
    exact ⟨T, hT⟩

end TauCeti
