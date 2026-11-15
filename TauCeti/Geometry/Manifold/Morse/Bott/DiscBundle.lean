/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Attachment
public import TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle
public import TauCeti.Geometry.Manifold.Morse.Bott.Tubular
import TauCeti.Topology.FiberBundle.Separation

/-!
# Attaching the negative disc bundle of a compact Morse–Bott submanifold

Let `i : S → M` be a compact nondegenerate critical submanifold of a smooth function `f` on a
boundaryless manifold, on the level `f = c`, and let `g` be a smooth fibre metric on its normal
bundle `ν`. The metric splits each normal space into the negative normal space `ν⁻`, on which the
normal Hessian `Hessₛ` is negative definite, and the positive normal space `ν⁺`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeNormalSpace`). The **negative disc
bundle** of size `ε` is `D_ε = {v ∈ ν⁻ | -½ Hessₛ (v, v) ≤ ε}`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeDiscBundle`); its fibres are closed
ellipsoids of dimension the index of the submanifold.

This file proves that crossing the critical level attaches the negative disc bundle
(`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`, in the
namespace `TauCeti.SmoothEmbedding`): there are a Morse–Bott normal form `Θ : ν → M` near the
zero section, with `f (Θ v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` such that for `0 < ε < ε₀`, if
the band `f⁻¹[c - ε, c + ε]` is compact and its critical points lie on the submanifold, then the
sublevel `{f ≤ c + ε}` strong deformation retracts onto `{f ≤ c - ε} ∪ Θ(D_ε)`. For an isolated
nondegenerate critical point the base is a point and this is Milnor's attachment of a cell of
dimension the index.

The normal form `Θ` is the Morse–Bott lemma on the normal bundle
(`IsNondegenerateCriticalSubmanifold.exists_morseBott_partialDiffeomorph_normalBundle`).
Writing a normal vector as `v = u + w` with `u ∈ ν⁻` and `w ∈ ν⁺`, the two parts are orthogonal
for the normal Hessian, so `f ∘ Θ = c - s + t` with `s = -½ Hessₛ (u, u) ≥ 0` and
`t = ½ Hessₛ (w, w) ≥ 0`. These are smooth on the total space, since the projections onto `ν⁻`
and `ν⁺` are (`IsNondegenerateCriticalSubmanifold.contMDiff_projection_negativeNormalSpace`) and so
is the quadratic form of the normal Hessian
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.contMDiff_normalHessian_apply_self`); rescaling
`(u, w) ↦ (a u, b w)` multiplies `s` by `a²` and `t` by `b²`. The tube of the attachment theorem
for a quadratic normal form (`TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`) is
the image under `Θ` of a sublevel `{s + 2t < m}`. Since `s + 2t` is positive off the zero section
and decreases along the rays `r ↦ r v`, `r ∈ [0, 1]`, which start on the zero section, such a
sublevel lies in any given compact neighbourhood of the compact zero section once `m` is small,
so its closed sublevels `{s + 2t ≤ 2ε}` are compact and lie in the source of `Θ`.

## Main definitions

* `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeDiscBundle`: the negative disc bundle of
  a critical submanifold relative to a fibre metric.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`:
  crossing the level of a compact Morse–Bott submanifold attaches its negative disc bundle, up to
  a strong deformation retraction.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.1 and 15.4.
-/

public section

noncomputable section

open Bundle Function Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

section Compactness

variable {X : Type*} [TopologicalSpace X]

/-- Let `q` be a continuous function which is positive off a compact set `Z`, and suppose every
point `x` lies in a preconnected set meeting `Z` on which `q ≤ q x`. Then for small `m > 0` the
sublevel `{q < m}` lies in any given open neighbourhood `U` of `Z`, and the closed sublevels
`{q ≤ δ}`, `δ < m`, are compact: they lie in a compact neighbourhood of `Z` inside `U`, on whose
boundary `q ≥ m`. -/
private theorem exists_pos_setOf_lt_subset_and_isCompact [LocallyCompactSpace X] [T2Space X]
    {Z U : Set X} (hZ : IsCompact Z) (hU : IsOpen U) (hZU : Z ⊆ U) {q : X → ℝ} (hq : Continuous q)
    (hqZ : ∀ x, q x ≤ 0 → x ∈ Z)
    (hpath : ∀ x, ∃ C : Set X, IsPreconnected C ∧ x ∈ C ∧ (C ∩ Z).Nonempty ∧ ∀ y ∈ C, q y ≤ q x) :
    ∃ m > 0, {x | q x < m} ⊆ U ∧ ∀ δ < m, IsCompact {x | q x ≤ δ} := by
  obtain ⟨N, hNc, hZN, hNU⟩ := exists_compact_between hZ hU hZU
  obtain ⟨m, hm, hmN⟩ : ∃ m, 0 < m ∧ ∀ x ∈ N \ interior N, m ≤ q x :=
    (hNc.diff isOpen_interior).exists_forall_le' hq.continuousOn fun x hx ↦
      not_le.1 fun hle ↦ hx.2 (hZN (hqZ x hle))
  -- A point with `q < m` is joined to `Z` without crossing the boundary of `N`.
  have hqN (x : X) (hx : q x < m) : x ∈ interior N := by
    obtain ⟨C, hC, hxC, hCZ, hCq⟩ := hpath x
    refine hC.subset_left_of_subset_union isOpen_interior hNc.isClosed.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) (fun y hy ↦ ?_)
      (hCZ.mono (inter_subset_inter_right _ hZN)) hxC
    by_cases hyN : y ∈ N
    · exact Or.inl (by_contra fun hint ↦ (hmN y ⟨hyN, hint⟩).not_gt ((hCq y hy).trans_lt hx))
    · exact Or.inr hyN
  refine ⟨m, hm, fun x hx ↦ hNU (interior_subset (hqN x hx)), fun δ hδ ↦ ?_⟩
  exact hNc.of_isClosed_subset (isClosed_le hq continuous_const) fun x hx ↦
    interior_subset (hqN x (lt_of_le_of_lt hx hδ))

end Compactness

section Transport

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- If a curve `γ` through `y` keeps `u` constant and `v` equal to `τ² b` near `τ = 1`, with
`b ≠ 0`, then its velocity at `τ = 1` is killed by `du` but not by `dv`. -/
private theorem exists_mfderiv_apply_eq_zero_and_ne_zero {u v : M → ℝ} {γ : ℝ → M} {y : M}
    {a b : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ) I γ 1) (hγy : γ 1 = y)
    (hu : MDifferentiableAt I 𝓘(ℝ) u y) (hv : MDifferentiableAt I 𝓘(ℝ) v y)
    (huγ : u ∘ γ =ᶠ[𝓝 1] fun _ ↦ a) (hvγ : v ∘ γ =ᶠ[𝓝 1] fun τ ↦ τ ^ 2 * b) (hb : b ≠ 0) :
    ∃ w : TangentSpace I y, mfderiv I 𝓘(ℝ) u y w = 0 ∧ mfderiv I 𝓘(ℝ) v y w ≠ 0 := by
  subst hγy
  have hdu := congrArg (fun L ↦ L (1 : ℝ)) (mfderiv_comp (I' := I) 1 hu hγ)
  have hdv := congrArg (fun L ↦ L (1 : ℝ)) (mfderiv_comp (I' := I) 1 hv hγ)
  rw [huγ.mfderiv_eq, mfderiv_const] at hdu
  rw [(((hasDerivAt_pow 2 (1 : ℝ)).mul_const b).hasFDerivAt.hasMFDerivAt.congr_of_eventuallyEq_abuse
    hvγ).mfderiv] at hdv
  refine ⟨mfderiv 𝓘(ℝ) I γ 1 (1 : ℝ), hdu.symm, fun h0 ↦ hb ?_⟩
  have h1 : ContinuousLinearMap.toSpanSingleton ℝ ((2 : ℕ) * 1 ^ (2 - 1) * b) (1 : ℝ) = 0 :=
    hdv.trans h0
  simpa using h1

variable {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {K : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]

/-- A scaling `ρ` of the positive directions of a subset `W` of the source of a partial
diffeomorphism `Θ`, carried to `Θ '' W`: it preserves `s ∘ Θ⁻¹`, multiplies `t ∘ Θ⁻¹` by `τ²`, is
the identity at `τ = 1` and fixes the points with `t ∘ Θ⁻¹ = 0`. -/
private theorem exists_continuousMap_image (Θ : PartialDiffeomorph K I X M ∞) {s t : X → ℝ}
    (ρ : ℝ → X → X) (hρ : Continuous fun p : ℝ × X ↦ ρ p.1 p.2) (hρs : ∀ b x, s (ρ b x) = s x)
    (hρt : ∀ b x, t (ρ b x) = b ^ 2 * t x) (hρ₁ : ∀ x, ρ 1 x = x)
    (hρ₀ : ∀ b x, t x = 0 → ρ b x = x) {W : Set X} (hWΘ : W ⊆ Θ.source)
    (hρW : ∀ τ : unitInterval, ∀ x ∈ W, ρ τ x ∈ W) :
    ∃ φ : C(unitInterval × Θ '' W, Θ '' W),
      (∀ τ (y : Θ '' W), s (Θ.toPartialEquiv.symm (φ (τ, y))) = s (Θ.toPartialEquiv.symm y)) ∧
      (∀ τ (y : Θ '' W),
        t (Θ.toPartialEquiv.symm (φ (τ, y))) = (τ : ℝ) ^ 2 * t (Θ.toPartialEquiv.symm y)) ∧
      (∀ y, φ (1, y) = y) ∧
      (∀ τ (y : Θ '' W), t (Θ.toPartialEquiv.symm y) = 0 → φ (τ, y) = y) := by
  have hWt : Θ '' W ⊆ Θ.target := image_subset_iff.2 fun x hx ↦ Θ.map_source (hWΘ hx)
  have hWsymm (y : M) (hy : y ∈ Θ '' W) : Θ.toPartialEquiv.symm y ∈ W := by
    obtain ⟨x, hx, rfl⟩ := hy
    rwa [Θ.left_inv (hWΘ hx)]
  have hcont : Continuous fun p : unitInterval × Θ '' W ↦ Θ.toPartialEquiv.symm p.2 :=
    Θ.symm.contMDiffOn.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_snd)
      fun p ↦ hWt p.2.2
  refine ⟨⟨fun p ↦ ⟨Θ (ρ p.1 (Θ.toPartialEquiv.symm p.2)),
      mem_image_of_mem _ (hρW p.1 _ (hWsymm _ p.2.2))⟩,
    (Θ.contMDiffOn.continuousOn.comp_continuous
      (hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk hcont))
      fun p ↦ hWΘ (hρW p.1 _ (hWsymm _ p.2.2))).subtype_mk _⟩, ?_, ?_, ?_, ?_⟩
  · rintro τ ⟨_, x, hx, rfl⟩
    simp only [ContinuousMap.coe_mk, Θ.left_inv (hWΘ hx), Θ.left_inv (hWΘ (hρW τ x hx)), hρs]
  · rintro τ ⟨_, x, hx, rfl⟩
    simp only [ContinuousMap.coe_mk, Θ.left_inv (hWΘ hx), Θ.left_inv (hWΘ (hρW τ x hx)), hρt]
  · rintro ⟨_, x, hx, rfl⟩
    simp only [ContinuousMap.coe_mk, Θ.left_inv (hWΘ hx), Set.Icc.coe_one, hρ₁]
  · rintro τ ⟨_, x, hx, rfl⟩ htx
    rw [Θ.left_inv (hWΘ hx)] at htx
    simp only [ContinuousMap.coe_mk, Θ.left_inv (hWΘ hx), hρ₀ _ x htx]

/-- Let `s` and `t` be smooth on `X`, and let `ρ b` preserve `s` and multiply `t` by `b²`, with
`ρ 1 = id`. At a point `x` of the source of `Θ` with `t x ≠ 0`, the velocity at `b = 1` of the
curve `b ↦ Θ (ρ b x)` is killed by the derivative of `s ∘ Θ⁻¹` but not by that of `t ∘ Θ⁻¹`. -/
private theorem exists_mfderiv_comp_symm_apply_eq_zero_and_ne_zero
    (Θ : PartialDiffeomorph K I X M ∞) {s t : X → ℝ} (hs : ContMDiff K 𝓘(ℝ) ∞ s)
    (ht : ContMDiff K 𝓘(ℝ) ∞ t) (ρ : ℝ → X → X) (hρ : Continuous fun p : ℝ × X ↦ ρ p.1 p.2)
    (hρd : ∀ x, MDifferentiableAt 𝓘(ℝ) K (fun b ↦ ρ b x) 1) (hρs : ∀ b x, s (ρ b x) = s x)
    (hρt : ∀ b x, t (ρ b x) = b ^ 2 * t x) (hρ₁ : ∀ x, ρ 1 x = x) {x : X} (hx : x ∈ Θ.source)
    (htx : t x ≠ 0) : ∃ v : TangentSpace I (Θ x),
      mfderiv I 𝓘(ℝ) (s ∘ Θ.toPartialEquiv.symm) (Θ x) v = 0 ∧
        mfderiv I 𝓘(ℝ) (t ∘ Θ.toPartialEquiv.symm) (Θ x) v ≠ 0 := by
  have hΘs : ContMDiffAt I K ∞ Θ.toPartialEquiv.symm (Θ x) :=
    Θ.symm.contMDiffOn.contMDiffAt (Θ.open_target.mem_nhds (Θ.map_source hx))
  have hev : ∀ᶠ b in 𝓝 (1 : ℝ), ρ b x ∈ Θ.source :=
    (hρ.comp (continuous_id.prodMk continuous_const)).continuousAt.preimage_mem_nhds
      (Θ.open_source.mem_nhds (by simpa [hρ₁] using hx))
  refine exists_mfderiv_apply_eq_zero_and_ne_zero (γ := fun b ↦ Θ (ρ b x)) (a := s x)
    ((Θ.mdifferentiableAt (by simp) (by rwa [hρ₁])).comp (I' := K) 1 (hρd x))
    (by simp only [hρ₁]) (((hs _).comp _ hΘs).mdifferentiableAt (by simp))
    (((ht _).comp _ hΘs).mdifferentiableAt (by simp)) (hev.mono fun b hb ↦ ?_)
    (hev.mono fun b hb ↦ ?_) htx
  · simp only [comp_apply, Θ.left_inv hb, hρs]
  · simp only [comp_apply, Θ.left_inv hb, hρt]

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}
  {c : ℝ}

/-- The attachment theorem `TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`, read
through a partial diffeomorphism `Θ : X → M`. On `X`, the functions `s, t ≥ 0` are smooth with
`f ∘ Θ = c - s + t`, and `ρ b` scales the positive directions: it preserves `s`, multiplies `t` by
`b²`, is the identity for `b = 1` and fixes the points with `t = 0`. If `W ⊆ X` is an open subset
of the source of `Θ` preserved by `ρ τ` for `τ ∈ [0, 1]`, containing the disc bundle
`{t = 0, s ≤ ε}`, whose part `{s + 2t ≤ 2ε}` is compact and whose image contains the critical
points of the compact band `f⁻¹[c - ε, c + ε]`, then `{f ≤ c + ε}` strong deformation retracts
onto `{f ≤ c - ε}` with the image of the disc bundle attached. -/
private theorem exists_sublevel_union_image_deformation_of_tube (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (Θ : PartialDiffeomorph K I X M ∞) {s t : X → ℝ} (hs : ContMDiff K 𝓘(ℝ) ∞ s)
    (ht : ContMDiff K 𝓘(ℝ) ∞ t) (hs₀ : ∀ x, 0 ≤ s x) (ht₀ : ∀ x, 0 ≤ t x)
    (hf : ∀ x ∈ Θ.source, f (Θ x) = c - s x + t x) (ρ : ℝ → X → X)
    (hρ : Continuous fun p : ℝ × X ↦ ρ p.1 p.2)
    (hρd : ∀ x, MDifferentiableAt 𝓘(ℝ) K (fun b ↦ ρ b x) 1) (hρs : ∀ b x, s (ρ b x) = s x)
    (hρt : ∀ b x, t (ρ b x) = b ^ 2 * t x) (hρ₁ : ∀ x, ρ 1 x = x)
    (hρ₀ : ∀ b x, t x = 0 → ρ b x = x) {W : Set X} (hWo : IsOpen W) (hWΘ : W ⊆ Θ.source)
    (hρW : ∀ τ : unitInterval, ∀ x ∈ W, ρ τ x ∈ W) {ε : ℝ} (hε : 0 < ε)
    (hD : ∀ x, t x = 0 → s x ≤ ε → x ∈ W) (hK : IsCompact {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε})
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ Θ '' W) :
    ∃ r : C({y | f y ≤ c + ε}, ↥({y | f y ≤ c + ε} ∩
        ({y | f y ≤ c - ε} ∪ Θ '' {x | t x = 0 ∧ s x ≤ ε}))),
      (∀ y, r (ContinuousMap.inclusion inter_subset_left y) = y) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id _) {y | (y : M) ∈ {y | f y ≤ c - ε} ∪ Θ '' {x | t x = 0 ∧ s x ≤ ε}}) := by
  have hΘs : ContMDiffOn I K ∞ Θ.toPartialEquiv.symm Θ.target := Θ.symm.contMDiffOn
  have hWt : Θ '' W ⊆ Θ.target := image_subset_iff.2 fun x hx ↦ Θ.map_source (hWΘ hx)
  have hWsymm (y : M) (hy : y ∈ Θ '' W) : Θ.toPartialEquiv.symm y ∈ W := by
    obtain ⟨x, hx, rfl⟩ := hy
    rwa [Θ.left_inv (hWΘ hx)]
  -- A condition on the points of `W` reads on `Θ '' W` through `Θ⁻¹`.
  have himage (p : X → Prop) :
      {y | y ∈ Θ '' W ∧ p (Θ.toPartialEquiv.symm y)} = Θ '' {x | x ∈ W ∧ p x} := by
    ext y
    refine ⟨fun ⟨hy, hpy⟩ ↦ ⟨_, ⟨hWsymm y hy, hpy⟩, Θ.right_inv (hWt hy)⟩, ?_⟩
    rintro ⟨x, ⟨hx, hpx⟩, rfl⟩
    rw [mem_ofPred_eq, Θ.left_inv (hWΘ hx)]
    exact ⟨mem_image_of_mem _ hx, hpx⟩
  have hWo' : IsOpen (Θ '' W) := by
    simpa [inter_eq_self_of_subset_right hWΘ] using
      Θ.toOpenPartialHomeomorph.isOpen_image_source_inter hWo
  -- The functions `s` and `t` read on `M`, and the scaling of the positive directions.
  set sM : M → ℝ := s ∘ Θ.toPartialEquiv.symm
  set tM : M → ℝ := t ∘ Θ.toPartialEquiv.symm
  have hsM : ContMDiffOn I 𝓘(ℝ) ∞ sM (Θ '' W) := hs.comp_contMDiffOn (hΘs.mono hWt)
  have htM : ContMDiffOn I 𝓘(ℝ) ∞ tM (Θ '' W) := ht.comp_contMDiffOn (hΘs.mono hWt)
  have hsΘ (x : X) (hx : x ∈ Θ.source) : sM (Θ x) = s x := by
    simp only [sM, comp_apply, Θ.left_inv hx]
  have htΘ (x : X) (hx : x ∈ Θ.source) : tM (Θ x) = t x := by
    simp only [tM, comp_apply, Θ.left_inv hx]
  obtain ⟨φ, hφs, hφt, hφ₁, hφ₀⟩ := exists_continuousMap_image Θ ρ hρ hρs hρt hρ₁ hρ₀ hWΘ hρW
  have hdir (y : M) (hy : y ∈ Θ '' W) (hty : tM y ≠ 0) : ∃ v : TangentSpace I y,
      mfderiv I 𝓘(ℝ) sM y v = 0 ∧ mfderiv I 𝓘(ℝ) tM y v ≠ 0 := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact exists_mfderiv_comp_symm_apply_eq_zero_and_ne_zero Θ hs ht ρ hρ hρd hρs hρt hρ₁
      (hWΘ hx) (by rwa [htΘ x (hWΘ hx)] at hty)
  have hKM : IsCompact {y | y ∈ Θ '' W ∧ sM y + 2 * tM y ≤ 2 * ε} := by
    rw [show {y | y ∈ Θ '' W ∧ sM y + 2 * tM y ≤ 2 * ε} =
        Θ '' {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε} from himage fun x ↦ s x + 2 * t x ≤ 2 * ε]
    exact hK.image_of_continuousOn (Θ.contMDiffOn.continuousOn.mono fun x hx ↦ hWΘ hx.1)
  have key := exists_sublevel_union_negativeDiscBundle_deformation hfs hWo' hsM htM
    (fun y _ ↦ hs₀ _) (fun y _ ↦ ht₀ _) ?_ hdir φ hφs hφt hφ₁ hφ₀ hε hKM hcompact hcrit
  · have hDW : {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε} = {x | t x = 0 ∧ s x ≤ ε} :=
      Set.ext fun x ↦ ⟨fun hx ↦ hx.2, fun hx ↦ ⟨hD x hx.1 hx.2, hx⟩⟩
    rwa [show {y | y ∈ Θ '' W ∧ tM y = 0 ∧ sM y ≤ ε} = Θ '' {x | t x = 0 ∧ s x ≤ ε} from
      hDW ▸ himage fun x ↦ t x = 0 ∧ s x ≤ ε] at key
  · rintro _ ⟨x, hx, rfl⟩
    rw [hf x (hWΘ hx), hsΘ x (hWΘ hx), htΘ x (hWΘ hx)]

/-- The attachment theorem read through a partial diffeomorphism `Θ : X → M` near a compact core
`Z`, for all small `ε > 0`. On `X`, the functions `s, t ≥ 0` are smooth, vanish together exactly
on `Z`, and satisfy `f ∘ Θ = c - s + t`; the maps `σ a b` rescale `s` by `a²` and `t` by `b²`,
and `σ 0 0` maps into `Z`. The tube is `{s + 2t < m}` for small `m > 0`. -/
private theorem exists_sublevel_union_image_deformation [LocallyCompactSpace X] [T2Space X]
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (Θ : PartialDiffeomorph K I X M ∞) {s t : X → ℝ}
    (hs : ContMDiff K 𝓘(ℝ) ∞ s) (ht : ContMDiff K 𝓘(ℝ) ∞ t) (hs₀ : ∀ x, 0 ≤ s x)
    (ht₀ : ∀ x, 0 ≤ t x) (hf : ∀ x ∈ Θ.source, f (Θ x) = c - s x + t x) {Z : Set X}
    (hZ : IsCompact Z) (hZΘ : Z ⊆ Θ.source) (hZst : ∀ x ∈ Z, s x = 0 ∧ t x = 0)
    (hstZ : ∀ x, s x = 0 → t x = 0 → x ∈ Z) (σ : ℝ → ℝ → X → X)
    (hσ : Continuous fun p : (ℝ × ℝ) × X ↦ σ p.1.1 p.1.2 p.2)
    (hσd : ∀ x, MDifferentiableAt 𝓘(ℝ) K (fun b ↦ σ 1 b x) 1)
    (hσs : ∀ a b x, s (σ a b x) = a ^ 2 * s x) (hσt : ∀ a b x, t (σ a b x) = b ^ 2 * t x)
    (hσ₁ : ∀ x, σ 1 1 x = x) (hσ₀ : ∀ b x, t x = 0 → σ 1 b x = x) (hσZ : ∀ x, σ 0 0 x ∈ Z) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
      criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ Θ '' Z →
      {x | t x = 0 ∧ s x ≤ ε} ⊆ Θ.source ∧
      ∃ r : C({y | f y ≤ c + ε}, ↥({y | f y ≤ c + ε} ∩
          ({y | f y ≤ c - ε} ∪ Θ '' {x | t x = 0 ∧ s x ≤ ε}))),
        (∀ y, r (ContinuousMap.inclusion inter_subset_left y) = y) ∧
        Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
          (ContinuousMap.id _)
          {y | (y : M) ∈ {y | f y ≤ c - ε} ∪ Θ '' {x | t x = 0 ∧ s x ≤ ε}}) := by
  set q : X → ℝ := fun x ↦ s x + 2 * t x with hq_def
  have hq : Continuous q := hs.continuous.add (continuous_const.mul ht.continuous)
  have hq_le (a b : ℝ) (ha : a ^ 2 ≤ 1) (hb : b ^ 2 ≤ 1) (x : X) : q (σ a b x) ≤ q x := by
    simp only [hq_def, hσs, hσt]
    nlinarith [hs₀ x, ht₀ x]
  -- The rays `a ↦ σ a a x`, `a ∈ [0, 1]`, join each point to the core, with `q` at most `q x`.
  obtain ⟨m, hm, hmΘ, hmK⟩ := exists_pos_setOf_lt_subset_and_isCompact hZ Θ.open_source hZΘ hq
    (fun x (hx : s x + 2 * t x ≤ 0) ↦
      hstZ x (by linarith [hs₀ x, ht₀ x]) (by linarith [hs₀ x, ht₀ x]))
    fun x ↦ ⟨(fun a ↦ σ a a x) '' Icc 0 1, isPreconnected_Icc.image _
      (hσ.comp ((continuous_id.prodMk continuous_id).prodMk continuous_const)).continuousOn,
      ⟨1, ⟨zero_le_one, le_rfl⟩, hσ₁ x⟩, ⟨σ 0 0 x, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, hσZ x⟩,
      by rintro _ ⟨a, ha, rfl⟩; exact hq_le a a (pow_le_one₀ ha.1 ha.2) (pow_le_one₀ ha.1 ha.2) x⟩
  refine ⟨m / 2, half_pos hm, fun ε hε hcompact hcrit ↦ ?_⟩
  have hεm : 2 * ε < m := by linarith [hε.2]
  have hD (x : X) (ht : t x = 0) (hs : s x ≤ ε) : q x < m := by
    simp only [hq_def, ht, mul_zero, add_zero]
    linarith [hε.1]
  refine ⟨fun x hx ↦ hmΘ (hD x hx.1 hx.2), exists_sublevel_union_image_deformation_of_tube hfs Θ
    hs ht hs₀ ht₀ hf (σ 1) (hσ.comp ((continuous_const.prodMk continuous_fst).prodMk
      continuous_snd)) hσd (fun b x ↦ by rw [hσs, one_pow, one_mul]) (hσt 1) hσ₁ hσ₀
    (W := {x | q x < m}) (isOpen_lt hq continuous_const) hmΘ
    (fun τ x hx ↦ (hq_le 1 τ (by norm_num) (pow_le_one₀ τ.2.1 τ.2.2) x).trans_lt hx) hε.1 hD ?_
    hcompact (hcrit.trans (image_mono fun x hx ↦ ?_))⟩
  · have hset : {x | x ∈ {x | q x < m} ∧ s x + 2 * t x ≤ 2 * ε} = {x | q x ≤ 2 * ε} :=
      Set.ext fun x ↦ ⟨fun hx ↦ hx.2, fun hx ↦ ⟨lt_of_le_of_lt hx hεm, hx⟩⟩
    exact hset ▸ hmK (2 * ε) hεm
  · simp only [mem_ofPred_eq, hq_def, (hZst x hx).1, (hZst x hx).2, mul_zero, add_zero, hm]

end Transport

namespace SmoothEmbedding

section DiscBundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0) {P : Type*}

namespace IsCriticalSubmanifold

variable (h : i.IsCriticalSubmanifold f) (P) (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)

/-- The **negative disc bundle** of a critical submanifold, of size `ε`, relative to a fibre metric
`g` on the normal spaces: the normal vectors `v` in the negative normal space with
`-½ Hessₛ (v, v) ≤ ε`, where `Hessₛ` is the normal Hessian. For a Morse–Bott submanifold the normal
Hessian is negative definite on the negative normal spaces, so for `ε > 0` each fibre is a closed
ellipsoid of dimension the Morse index. -/
def negativeDiscBundle (ε : ℝ) : Set (TotalSpace P fun s ↦ i.NormalSpace s hn) :=
  {x | x.2 ∈ h.negativeNormalSpace hn g x.proj ∧ -(2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ≤ ε}

variable {h P g} in
@[simp]
theorem mem_negativeDiscBundle {ε : ℝ} {x : TotalSpace P fun s ↦ i.NormalSpace s hn} :
    x ∈ h.negativeDiscBundle hn P g ε ↔
      x.2 ∈ h.negativeNormalSpace hn g x.proj ∧ -(2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ≤ ε :=
  Iff.rfl

end IsCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable [FiniteDimensional ℝ E] (h : i.IsNondegenerateCriticalSubmanifold f)
  (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)

/-- The part of a normal vector in the negative normal space, along the positive one. -/
private def negPart (s : S) : i.NormalSpace s hn →ₗ[ℝ] i.NormalSpace s hn :=
  (h.negativeNormalSpace hn g s).projection (h.positiveNormalSpace hn g s)
    (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s)

/-- The part of a normal vector in the positive normal space, along the negative one. -/
private def posPart (s : S) : i.NormalSpace s hn →ₗ[ℝ] i.NormalSpace s hn :=
  (h.positiveNormalSpace hn g s).projection (h.negativeNormalSpace hn g s)
    (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s).symm

/-- Minus half the normal Hessian of the negative part of a normal vector. -/
private def negSq (x : TotalSpace P fun s ↦ i.NormalSpace s hn) : ℝ :=
  -(2⁻¹ * h.normalHessian hn x.proj (h.negPart hn g x.proj x.2) (h.negPart hn g x.proj x.2))

/-- Half the normal Hessian of the positive part of a normal vector. -/
private def posSq (x : TotalSpace P fun s ↦ i.NormalSpace s hn) : ℝ :=
  2⁻¹ * h.normalHessian hn x.proj (h.posPart hn g x.proj x.2) (h.posPart hn g x.proj x.2)

/-- Rescale the negative part of a normal vector by `a` and its positive part by `b`. -/
private def rescale (a b : ℝ) (x : TotalSpace P fun s ↦ i.NormalSpace s hn) :
    TotalSpace P fun s ↦ i.NormalSpace s hn :=
  ⟨x.proj, a • h.negPart hn g x.proj x.2 + b • h.posPart hn g x.proj x.2⟩

variable {s : S} (v : i.NormalSpace s hn) (x : TotalSpace P fun s ↦ i.NormalSpace s hn)

private theorem negSq_mk : h.negSq hn g (⟨s, v⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn) =
    -(2⁻¹ * h.normalHessian hn s (h.negPart hn g s v) (h.negPart hn g s v)) :=
  rfl

private theorem posSq_mk : h.posSq hn g (⟨s, v⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn) =
    2⁻¹ * h.normalHessian hn s (h.posPart hn g s v) (h.posPart hn g s v) :=
  rfl

private theorem rescale_def (a b : ℝ) : h.rescale hn g a b x =
    ⟨x.proj, a • h.negPart hn g x.proj x.2 + b • h.posPart hn g x.proj x.2⟩ :=
  rfl

private theorem negPart_mem : h.negPart hn g s v ∈ h.negativeNormalSpace hn g s :=
  Submodule.projection_apply_mem _ v

private theorem posPart_mem : h.posPart hn g s v ∈ h.positiveNormalSpace hn g s :=
  Submodule.projection_apply_mem _ v

private theorem negPart_add_posPart : h.negPart hn g s v + h.posPart hn g s v = v :=
  Submodule.projection_add_projection_eq_self _ v

private theorem posPart_eq_zero_iff : h.posPart hn g s v = 0 ↔ v ∈ h.negativeNormalSpace hn g s :=
  Submodule.projection_apply_eq_zero_iff _

/-- The normal Hessian of a normal vector is the sum of its values on the two parts, which are
orthogonal for it. -/
private theorem normalHessian_eq_add :
    h.normalHessian hn s v v = h.normalHessian hn s (h.negPart hn g s v) (h.negPart hn g s v) +
      h.normalHessian hn s (h.posPart hn g s v) (h.posPart hn g s v) := by
  have h0 := h.normalHessian_eq_zero_of_mem_negativeNormalSpace hn g (h.negPart_mem hn g v)
    (h.posPart_mem hn g v)
  have h0' : h.normalHessian hn s (h.posPart hn g s v) (h.negPart hn g s v) = 0 := by
    rw [(h.isSymm_normalHessian hn s).eq, h0]
  conv_lhs => rw [← h.negPart_add_posPart hn g v]
  simp only [map_add, LinearMap.add_apply, h0, h0']
  ring

private theorem negSq_nonneg : 0 ≤ h.negSq hn g x := by
  by_cases hv : h.negPart hn g x.proj x.2 = 0
  · simp [negSq, hv]
  · have := h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn g
      (h.negPart_mem hn g x.2) hv
    simp only [negSq]
    linarith

private theorem posSq_nonneg : 0 ≤ h.posSq hn g x := by
  by_cases hv : h.posPart hn g x.proj x.2 = 0
  · simp [posSq, hv]
  · have := h.normalHessian_apply_self_pos_of_mem_positiveNormalSpace hn g
      (h.posPart_mem hn g x.2) hv
    simp only [posSq]
    linarith

private theorem negPart_eq_zero (hx : h.negSq hn g x = 0) : h.negPart hn g x.proj x.2 = 0 := by
  by_contra hne
  have := h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn g
    (h.negPart_mem hn g x.2) hne
  simp only [negSq] at hx
  linarith

private theorem posPart_eq_zero (hx : h.posSq hn g x = 0) : h.posPart hn g x.proj x.2 = 0 := by
  by_contra hne
  have := h.normalHessian_apply_self_pos_of_mem_positiveNormalSpace hn g
    (h.posPart_mem hn g x.2) hne
  simp only [posSq] at hx
  linarith

/-- Half the normal Hessian is `-negSq + posSq`. -/
private theorem two_inv_mul_normalHessian :
    2⁻¹ * h.normalHessian hn x.proj x.2 x.2 = -h.negSq hn g x + h.posSq hn g x := by
  rw [negSq, posSq, h.normalHessian_eq_add hn g x.2]
  ring

private theorem negPart_smul_add_smul (a b : ℝ) :
    h.negPart hn g s (a • h.negPart hn g s v + b • h.posPart hn g s v) =
      a • h.negPart hn g s v := by
  have h₁ : h.negPart hn g s (h.negPart hn g s v) = h.negPart hn g s v :=
    Submodule.projection_apply_of_mem_left _ (h.negPart_mem hn g v)
  have h₂ : h.negPart hn g s (h.posPart hn g s v) = 0 :=
    Submodule.projection_apply_of_mem_right _ (h.posPart_mem hn g v)
  rw [map_add, map_smul, map_smul, h₁, h₂, smul_zero, add_zero]

private theorem posPart_smul_add_smul (a b : ℝ) :
    h.posPart hn g s (a • h.negPart hn g s v + b • h.posPart hn g s v) =
      b • h.posPart hn g s v := by
  have h₁ : h.posPart hn g s (h.negPart hn g s v) = 0 :=
    Submodule.projection_apply_of_mem_right _ (h.negPart_mem hn g v)
  have h₂ : h.posPart hn g s (h.posPart hn g s v) = h.posPart hn g s v :=
    Submodule.projection_apply_of_mem_left _ (h.posPart_mem hn g v)
  rw [map_add, map_smul, map_smul, h₁, h₂, smul_zero, zero_add]

private theorem negSq_rescale (a b : ℝ) :
    h.negSq hn g (h.rescale hn g a b x) = a ^ 2 * h.negSq hn g x := by
  rw [rescale_def, negSq_mk, h.negPart_smul_add_smul, negSq]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

private theorem posSq_rescale (a b : ℝ) :
    h.posSq hn g (h.rescale hn g a b x) = b ^ 2 * h.posSq hn g x := by
  rw [rescale_def, posSq_mk, h.posPart_smul_add_smul, posSq]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

private theorem rescale_one_one : h.rescale hn g 1 1 x = x := by
  simp only [rescale, one_smul, h.negPart_add_posPart]

private theorem rescale_one_of_posSq_eq_zero (b : ℝ) (hx : h.posSq hn g x = 0) :
    h.rescale hn g 1 b x = x := by
  conv_rhs => rw [← h.rescale_one_one hn g x]
  simp only [rescale, h.posPart_eq_zero hn g x hx, smul_zero]

private theorem rescale_zero_zero :
    h.rescale hn g 0 0 x = zeroSection P (fun s ↦ i.NormalSpace s hn) x.proj := by
  simp [rescale, zeroSection]

private theorem eq_zeroSection_of_negSq_eq_zero (hs : h.negSq hn g x = 0)
    (ht : h.posSq hn g x = 0) : zeroSection P (fun s ↦ i.NormalSpace s hn) x.proj = x := by
  rw [← h.rescale_zero_zero hn g x]
  conv_rhs => rw [← h.rescale_one_one hn g x]
  simp only [rescale, h.negPart_eq_zero hn g x hs, h.posPart_eq_zero hn g x ht, smul_zero]

private theorem negSq_zeroSection (s : S) :
    h.negSq hn g (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = 0 := by
  rw [zeroSection, negSq_mk, map_zero, map_zero, mul_zero, neg_zero]

private theorem posSq_zeroSection (s : S) :
    h.posSq hn g (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = 0 := by
  rw [zeroSection, posSq_mk, map_zero, map_zero, mul_zero]

/-- The disc bundle `{t = 0, s ≤ ε}` of the normal form is the negative disc bundle. -/
private theorem setOf_posSq_eq_zero_and_negSq_le (ε : ℝ) :
    {x | h.posSq hn g x = 0 ∧ h.negSq hn g x ≤ ε} = h.negativeDiscBundle hn P g ε := by
  ext x
  rw [IsCriticalSubmanifold.mem_negativeDiscBundle, ← h.posPart_eq_zero_iff hn g]
  have hH (hp : h.posPart hn g x.proj x.2 = 0) :
      -(2⁻¹ * h.normalHessian hn x.proj x.2 x.2) = h.negSq hn g x := by
    rw [h.two_inv_mul_normalHessian hn g x, posSq, hp]
    simp
  refine ⟨fun ⟨ht, hs⟩ ↦ ⟨h.posPart_eq_zero hn g x ht, by rwa [hH (h.posPart_eq_zero hn g x ht)]⟩,
    fun ⟨hp, hs⟩ ↦ ⟨by simp [posSq, hp], by rwa [hH hp] at hs⟩⟩

end IsNondegenerateCriticalSubmanifold

end DiscBundle

section Attachment

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {E' H' S P : Type*} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] [NormedAddCommGroup P]
  [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M}
  (hn : (∞ : ℕ∞ω) ≠ 0)

namespace IsNondegenerateCriticalSubmanifold

/-- The functions `negSq` and `posSq` are smooth on the total space of the normal bundle, and the
rescalings are jointly smooth in the scales and the normal vector. -/
private theorem contMDiff_negSq_posSq_rescale (h : i.IsNondegenerateCriticalSubmanifold f)
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ContMDiff (J.prod 𝓘(ℝ, P)) 𝓘(ℝ) ∞ (h.negSq (P := P) hn g.toRiemannianMetric) ∧
      ContMDiff (J.prod 𝓘(ℝ, P)) 𝓘(ℝ) ∞ (h.posSq (P := P) hn g.toRiemannianMetric) ∧
      ContMDiff (𝓘(ℝ, ℝ × ℝ).prod (J.prod 𝓘(ℝ, P))) (J.prod 𝓘(ℝ, P)) ∞
        fun p : (ℝ × ℝ) × TotalSpace P (fun s ↦ i.NormalSpace s hn) ↦
          h.rescale hn g.toRiemannianMetric p.1.1 p.1.2 p.2 := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := by simpa using (inferInstance : IsManifold J ∞ S)
  have hk : (∞ : ℕ∞ω) + 1 ≤ ∞ := by simp
  have hf2 (s : S) : ContMDiffAt I 𝓘(ℝ) (∞ + 2) f (i s) := (hfs (i s)).of_le (by simp)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  set X := TotalSpace P fun s ↦ i.NormalSpace s hn
  have hneg := h.contMDiff_projection_negativeNormalSpace hn hk hf2 hdim g
  have hpos := h.contMDiff_projection_positiveNormalSpace hn hk hf2 hdim g
  have hH := h.toIsCriticalSubmanifold.contMDiff_normalHessian_apply_self hn hk hf2 hdim
  refine ⟨(contMDiff_const.mul (hH.comp hneg)).neg, contMDiff_const.mul (hH.comp hpos),
    fun p₀ ↦ ?_⟩
  have h1 : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod (J.prod 𝓘(ℝ, P))) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun p : (ℝ × ℝ) × X ↦ p.1) p₀ := contMDiffAt_fst
  have h2 : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod (J.prod 𝓘(ℝ, P))) (J.prod 𝓘(ℝ, P)) ∞
      (fun p : (ℝ × ℝ) × X ↦ p.2) p₀ := contMDiffAt_snd
  have hA := (Bundle.contMDiffAt_totalSpace_iff.mp (hneg p₀.2)).2.comp p₀ h2
  have hB := (Bundle.contMDiffAt_totalSpace_iff.mp (hpos p₀.2)).2.comp p₀ h2
  have ha := (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ)).contMDiff.contMDiffAt.comp p₀ h1
  have hb := (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ)).contMDiff.contMDiffAt.comp p₀ h1
  have hproj : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod (J.prod 𝓘(ℝ, P))) J ∞
      (fun p : (ℝ × ℝ) × X ↦ p.2.proj) p₀ := (Bundle.contMDiff_proj _).contMDiffAt.comp p₀ h2
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨hproj, ((ha.smul hA).add (hb.smul hB)).congr_of_eventuallyEq ?_⟩
  have he := mem_baseSet_trivializationAt P (fun s ↦ i.NormalSpace s hn) p₀.2.proj
  filter_upwards [((FiberBundle.continuous_proj P _).comp continuous_snd).continuousAt
    |>.preimage_mem_nhds ((trivializationAt P _ _).open_baseSet.mem_nhds he)] with p hp
  replace hp : p.2.proj ∈ (trivializationAt P (fun s ↦ i.NormalSpace s hn) p₀.2.proj).baseSet := hp
  -- In the trivialization, the fibre coordinate is linear on the fibre over `p.2.proj`.
  have hlin (v : i.NormalSpace p.2.proj hn) :
      (trivializationAt P (fun s ↦ i.NormalSpace s hn) p₀.2.proj ⟨p.2.proj, v⟩).2 =
        (trivializationAt P (fun s ↦ i.NormalSpace s hn) p₀.2.proj).linearMapAt ℝ p.2.proj v := by
    rw [Trivialization.coe_linearMapAt_of_mem _ hp]
  simp only [rescale, negPart, posPart, TotalSpace.mk', Pi.add_apply, Pi.smul_apply', comp_apply,
    hlin, map_add, map_smul]

/-- **Crossing the level of a compact Morse–Bott submanifold attaches its negative disc bundle.**
Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on a Hausdorff,
second-countable, finite-dimensional, boundaryless manifold, with `S` compact and nonempty and
`f = c` along `i`, and let `g` be a smooth fibre metric on the normal bundle of `i`.

Then there is a smooth partial diffeomorphism `Θ` from the total space of the normal bundle to
`M`, defined on a neighbourhood of the zero section and sending it to `i`, which puts `f` in the
Morse–Bott normal form `f (Θ v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` with the following
property. Let `0 < ε < ε₀` be such that the band `f⁻¹[c - ε, c + ε]` is compact and all its
critical points lie on `i`. Then the negative disc bundle `D_ε` relative to `g`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeDiscBundle`) lies in the source of `Θ`, and
`{f ≤ c - ε} ∪ Θ(D_ε)` is a strong deformation retract of `{f ≤ c + ε}`: there is a retraction of
`{f ≤ c + ε}` onto it, and a homotopy in `{f ≤ c + ε}` from this retraction to the identity which
fixes it pointwise. -/
theorem exists_sublevel_union_negativeDiscBundle_deformation [T2Space M]
    [SecondCountableTopology M] [J.Boundaryless] [CompactSpace S] [Nonempty S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞,
      (∀ s, zeroSection P (fun s ↦ i.NormalSpace s hn) s ∈ Θ.source) ∧
      (∀ s, Θ (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = i s) ∧
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
        criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
        h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source ∧
        ∃ r : C({y | f y ≤ c + ε}, ↥({y | f y ≤ c + ε} ∩
            ({y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε))),
          (∀ y, r (ContinuousMap.inclusion inter_subset_left y) = y) ∧
          Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
            (ContinuousMap.id _) {y | (y : M) ∈
              {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε}) := by
  have : T2Space S := i.isEmbedding.t2Space
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : LocallyCompactSpace (ModelProd H' P) := (J.prod 𝓘(ℝ, P)).locallyCompactSpace
  have : LocallyCompactSpace (TotalSpace P fun s ↦ i.NormalSpace s hn) :=
    ChartedSpace.locallyCompactSpace (ModelProd H' P) _
  -- The Morse–Bott lemma on the normal bundle.
  obtain ⟨Θ, hΘz, hΘi, -, hΘf⟩ := h.exists_morseBott_partialDiffeomorph_normalBundle hn
    (k := ⊤) (by simp) hdim isOpen_univ (subset_univ _) (hfs.contMDiffOn.of_le (by simp))
  refine ⟨Θ, hΘz, hΘi, fun x hx ↦ by rw [hΘf x hx, hc], ?_⟩
  obtain ⟨hs, ht, hσ⟩ := h.contMDiff_negSq_posSq_rescale hn hfs hdim g
  set gR := g.toRiemannianMetric
  -- The curves `b ↦ σ 1 b x` are smooth.
  have hσd (x : TotalSpace P fun s ↦ i.NormalSpace s hn) :
      MDifferentiableAt 𝓘(ℝ) (J.prod 𝓘(ℝ, P)) (fun b ↦ h.rescale hn gR 1 b x) 1 :=
    ((hσ.comp ((contDiff_const.prodMk contDiff_id).contMDiff.prodMk contMDiff_const)) 1)
      |>.mdifferentiableAt (by simp)
  obtain ⟨ε₀, hε₀, hmain⟩ := exists_sublevel_union_image_deformation hfs Θ hs ht
    (h.negSq_nonneg hn gR) (h.posSq_nonneg hn gR)
    (fun x hx ↦ by rw [hΘf x hx, hc, h.two_inv_mul_normalHessian hn gR x]; ring)
    (isCompact_range (Bundle.contMDiff_zeroSection (n := ∞) (IB := J) _ _).continuous)
    (by rintro _ ⟨s, rfl⟩; exact hΘz s)
    (by rintro _ ⟨s, rfl⟩; exact ⟨h.negSq_zeroSection hn gR s, h.posSq_zeroSection hn gR s⟩)
    (fun x hs ht ↦ ⟨x.proj, h.eq_zeroSection_of_negSq_eq_zero hn gR x hs ht⟩)
    (h.rescale hn gR) hσ.continuous hσd (fun a b x ↦ h.negSq_rescale hn gR x a b)
    (fun a b x ↦ h.posSq_rescale hn gR x a b) (h.rescale_one_one hn gR)
    (fun b x hx ↦ h.rescale_one_of_posSq_eq_zero hn gR x b hx)
    (fun x ↦ ⟨x.proj, (h.rescale_zero_zero hn gR x).symm⟩)
  refine ⟨ε₀, hε₀, fun ε hε hcomp hcrit ↦ ?_⟩
  have hZ : range i = Θ '' range (zeroSection P fun s ↦ i.NormalSpace s hn) := by
    rw [← range_comp]
    exact congrArg range (funext fun s ↦ (hΘi s).symm)
  rw [← h.setOf_posSq_eq_zero_and_negSq_le hn gR ε]
  exact hmain ε hε hcomp (hZ ▸ hcrit)

end IsNondegenerateCriticalSubmanifold

end Attachment

end SmoothEmbedding

end TauCeti
