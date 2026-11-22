/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Integrable
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Chart
import TauCeti.Topology.ConnectedComponents

/-!
# Saturated neighbourhoods of a compact regular Liouville torus

Let `σ` be a symplectic form on a boundaryless manifold `M` of dimension `2 |ι|`, and let
`F : M → (ι → ℝ)` be a smooth family of pairwise Poisson-commuting functions. Let `L` be the
connected component of `x` in its level `F⁻¹(F x)`, and suppose that `L` is compact and consists of
regular points of `F`. The other components of this level need not be compact or regular.

This file shows that `L` has arbitrarily small open neighbourhoods `V` which are *saturated*: `V`
is a union of whole connected components of levels of `F`, each of them a compact component made of
regular points, and `F` is proper from `V` onto the open set `D = F(V)`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_inter_preimage_singleton_eq_connectedComponentIn`).
Precisely, for every neighbourhood `W` of `L` and every neighbourhood `N` of `F x` there are open
sets `V ⊆ W` and `D ⊆ N` with `L ⊆ V` and `F(V) = D`, such that

* every point of `V` is a regular point of `F`;
* for `y ∈ V`, the part `V ∩ F⁻¹(F y)` of the level through `y` lying in `V` is the whole connected
  component of `y` in `F⁻¹(F y)`;
* `V ∩ F⁻¹(K)` is compact for every compact `K ⊆ D`; in particular the components in `V` are
  compact.

The neighbourhood is the image `V = Ψ(ℝ^ι × D)` of the local action-angle coordinates `Ψ` near `L`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact`),
for a small open set `D` of values. Since `F (Ψ(θ, c)) = c` and `Ψ` is `2π`-periodic in the
angles, the part of `V` over a set `K ⊆ D` is the image of the compact set `[0, 2π]^ι × K`, and the
part over a single value `c` is the image of the connected set `ℝ^ι × {c}`. It is open in the level
because `V` is open, and closed because it is compact, so it is a connected component of the level.

Two consequences are the ones used in the Liouville–Arnold theorem.

* **Functions of the integrals.** For an integrable system `F`, a function that Poisson-commutes
  with every `F_i` on `V` is `ψ ∘ F` on all of `V`, for a function `ψ` as smooth as it is
  (`TauCeti.SmoothTwoForm.IsIntegrableSystem.exists_eqOn_comp_of_isCompact`). This fails on
  neighbourhoods with disconnected fibres, which is why saturation is needed.
* **Completeness.** On the open submanifold `V`, the Hamiltonian vector field of every `C²` function
  Poisson-commuting with the `F_i` is complete
  (`IsSymplectic.exists_opens_isCompleteVectorField_hamiltonianVectorField_of_isCompact`),
  since its integral curves stay in the compact components of the levels in `V`. In particular each
  component in `V` is invariant under the full Hamiltonian flows of the `F_i`.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.exists_inter_preimage_singleton_eq_connectedComponentIn`:
  arbitrarily small saturated open neighbourhoods of a compact regular component, on which `F` is
  proper onto an open set of values.
* `TauCeti.SmoothTwoForm.IsIntegrableSystem.exists_eqOn_comp_of_isCompact`: on such a
  neighbourhood, functions in involution with an integrable system are functions of its integrals.
* `IsSymplectic.exists_opens_isCompleteVectorField_hamiltonianVectorField_of_isCompact`:
  on such a neighbourhood, Hamiltonian vector fields of functions in involution with `F` are
  complete.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49.
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1 (the neighbourhood of a compact regular fibre as a torus fibration).
-/

public section

open Set Filter Module Topology Real TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι] {F : M → ι → ℝ}

namespace IsSymplectic

/-! ### The image of action-angle coordinates over an open set of values -/

section Image

variable {Ψ : (ι → ℝ) × (ι → ℝ) → M} {D : Set (ι → ℝ)}

omit [TopologicalSpace M] [T2Space M] [Fintype ι] in
/-- If `F (Ψ(θ, c)) = c` for `c ∈ D`, the part of `Ψ(ℝ^ι × D)` over a set `K` of values is
`Ψ(ℝ^ι × (D ∩ K))`. -/
private theorem image_univ_prod_inter_preimage (hFΨ : ∀ c ∈ D, ∀ θ, F (Ψ (θ, c)) = c)
    (K : Set (ι → ℝ)) : Ψ '' (univ ×ˢ D) ∩ F ⁻¹' K = Ψ '' (univ ×ˢ (D ∩ K)) := by
  ext y
  constructor
  · rintro ⟨⟨⟨θ, c⟩, ⟨-, hc⟩, rfl⟩, hy⟩
    exact ⟨(θ, c), ⟨trivial, hc, hFΨ c hc θ ▸ hy⟩, rfl⟩
  · rintro ⟨⟨θ, c⟩, ⟨-, hc, hcK⟩, rfl⟩
    exact ⟨⟨(θ, c), ⟨trivial, hc⟩, rfl⟩, by rwa [mem_preimage, hFΨ c hc θ]⟩

omit [TopologicalSpace M] [T2Space M] [Fintype ι] in
/-- If `Ψ` is `2π`-periodic in the angles over `D`, its values over `s ⊆ D` are already taken at
angles in the cube `[0, 2π]^ι`. -/
private theorem image_univ_prod_eq_image_Icc_prod
    (hper : ∀ c ∈ D, ∀ θ (m : ι → ℤ), Ψ (θ + fun i ↦ 2 * π * m i, c) = Ψ (θ, c))
    {s : Set (ι → ℝ)} (hs : s ⊆ D) :
    Ψ '' (univ ×ˢ s) = Ψ '' ((Icc 0 fun _ ↦ 2 * π) ×ˢ s) := by
  refine (image_mono (prod_mono (subset_univ _) le_rfl)).antisymm' ?_
  rintro _ ⟨⟨θ, c⟩, ⟨-, hc⟩, rfl⟩
  -- reduce each angle modulo `2π` into `[0, 2π)`
  have hp : (0 : ℝ) < 2 * π := by positivity
  refine ⟨(fun i ↦ toIcoMod hp 0 (θ i), c), ⟨⟨fun i ↦ (toIcoMod_mem_Ico' hp (θ i)).1,
    fun i ↦ (toIcoMod_mem_Ico' hp (θ i)).2.le⟩, hc⟩, ?_⟩
  have hθ : ((fun i ↦ toIcoMod hp 0 (θ i)) + fun i ↦ 2 * π * toIcoDiv hp 0 (θ i)) = θ := by
    funext i
    have := toIcoMod_add_toIcoDiv_zsmul hp 0 (θ i)
    rw [zsmul_eq_mul] at this
    simp only [Pi.add_apply]
    linear_combination this
  exact (hper c (hs hc) _ _).symm.trans (congrArg (fun t ↦ Ψ (t, c)) hθ)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [BoundarylessManifold I M] in
/-- **The image of action-angle coordinates over an open set of values is saturated.** Let `Ψ` be
a map, `2π`-periodic in the angles, with `F (Ψ(θ, c)) = c` and which is a local diffeomorphism at
every `(θ, c)` with `c` in an open set `D`. Then `V = Ψ(ℝ^ι × D)` is open with `F(V) = D`, consists
of regular points of `F`, meets the level through each of its points in the connected component of
that point, and meets the preimage of each compact `K ⊆ D` in a compact set. -/
private theorem image_univ_prod_saturated (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F) (hDo : IsOpen D)
    (hFΨ : ∀ c ∈ D, ∀ θ, F (Ψ (θ, c)) = c)
    (hloc : ∀ c ∈ D, ∀ θ, IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ (θ, c))
    (hper : ∀ c ∈ D, ∀ θ (m : ι → ℤ), Ψ (θ + fun i ↦ 2 * π * m i, c) = Ψ (θ, c)) :
    IsOpen (Ψ '' (univ ×ˢ D)) ∧ F '' (Ψ '' (univ ×ˢ D)) = D ∧
      (∀ y ∈ Ψ '' (univ ×ˢ D), IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y) ∧
      (∀ y ∈ Ψ '' (univ ×ˢ D),
        Ψ '' (univ ×ˢ D) ∩ F ⁻¹' {F y} = connectedComponentIn (F ⁻¹' {F y}) y) ∧
      ∀ K ⊆ D, IsCompact K → IsCompact (Ψ '' (univ ×ˢ D) ∩ F ⁻¹' K) := by
  have hcont : ContinuousOn Ψ (univ ×ˢ D) := fun z hz ↦
    (hloc z.2 hz.2 z.1).contMDiffAt.continuousAt.continuousWithinAt
  have hcompact (K : Set (ι → ℝ)) (hKD : K ⊆ D) (hK : IsCompact K) :
      IsCompact (Ψ '' (univ ×ˢ D) ∩ F ⁻¹' K) := by
    rw [image_univ_prod_inter_preimage hFΨ, inter_eq_self_of_subset_right hKD,
      image_univ_prod_eq_image_Icc_prod hper hKD]
    exact (isCompact_Icc.prod hK).image_of_continuousOn (hcont.mono (prod_mono (subset_univ _) hKD))
  have hFV : F '' (Ψ '' (univ ×ˢ D)) = D := by
    ext c
    refine ⟨?_, fun hc ↦ ⟨Ψ (0, c), ⟨(0, c), ⟨trivial, hc⟩, rfl⟩, hFΨ c hc 0⟩⟩
    rintro ⟨_, ⟨⟨θ, c'⟩, ⟨-, hc'⟩, rfl⟩, rfl⟩
    rwa [hFΨ c' hc' θ]
  -- `V` is open, since `Ψ` is a local homeomorphism on the open set `ℝ^ι × D`
  have hVo : IsOpen (Ψ '' (univ ×ˢ D)) := by
    have hlh : IsLocalHomeomorphOn Ψ (univ ×ˢ D) :=
      IsLocalDiffeomorphOn.isLocalHomeomorphOn (I := 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))) (J := I)
        (n := ∞) fun z ↦ hloc z.val.snd z.property.2 z.val.fst
    refine isOpen_iff_mem_nhds.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [← hlh.map_nhds_eq hz]
    exact image_mem_map ((isOpen_univ.prod hDo).mem_nhds hz)
  refine ⟨hVo, hFV, ?_, fun y hy ↦ ?_, hcompact⟩
  · -- near `(θ, c)`, `F ∘ Ψ` is the projection to the values, which is regular
    rintro _ ⟨⟨θ, c⟩, ⟨-, hc⟩, rfl⟩
    have heq : F ∘ Ψ =ᶠ[𝓝 (θ, c)] Prod.snd :=
      eventually_of_mem ((isOpen_univ.prod hDo).mem_nhds ⟨trivial, hc⟩)
        fun z hz ↦ hFΨ z.2 hz.2 z.1
    have hsnd : IsRegularPoint 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) 𝓘(ℝ, ι → ℝ) Prod.snd (θ, c) := by
      rw [isRegularPoint_iff_surjective_fderiv, fderiv_snd]
      exact Prod.snd_surjective
    exact (hsnd.congr_of_eventuallyEq heq).of_comp (hF.contMDiffAt.mdifferentiableAt (by simp))
      ((hloc c hc θ).mdifferentiableAt (by simp))
  · -- the part of the level of `y` in `V` is the connected image of `ℝ^ι × {F y}`, and compact
    have hyD : F y ∈ D := hFV ▸ mem_image_of_mem F hy
    refine (IsPreconnected.connectedComponentIn_eq_of_closure_inter_subset
      (S := Ψ '' (univ ×ˢ D) ∩ F ⁻¹' {F y}) ?_ ⟨hy, rfl⟩ hVo rfl
      fun _ hz ↦ (hcompact _ (singleton_subset_iff.2 hyD) isCompact_singleton).isClosed
        |>.closure_subset hz.1).symm
    rw [image_univ_prod_inter_preimage hFΨ, inter_eq_self_of_subset_right
      (singleton_subset_iff.2 hyD)]
    exact (isPreconnected_univ.prod isPreconnected_singleton).image Ψ
      (hcont.mono (prod_mono le_rfl (singleton_subset_iff.2 hyD)))

end Image

/-- **Saturated neighbourhoods of a compact regular Liouville torus.** On a symplectic manifold
of dimension `2 · |ι|`, let `F` be a smooth family of pairwise Poisson-commuting functions, and let
the connected component `L` of `x` in its level `F⁻¹(F x)` be compact and consist of regular points
of `F`. Then inside any neighbourhood `W` of `L` and over any neighbourhood `N` of `F x` there are
open sets `V ⊆ W` and `D ⊆ N` with `L ⊆ V` and `F(V) = D` such that every point of `V` is a regular
point of `F`, the part of `V` in the level through any `y ∈ V` is the connected component of `y` in
that level, and `F` is proper from `V` onto `D`: `V ∩ F⁻¹(K)` is compact for every compact
`K ⊆ D`. -/
theorem exists_inter_preimage_singleton_eq_connectedComponentIn (hσ : σ.IsSymplectic)
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F) (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) {W : Set M}
    (hW : W ∈ 𝓝ˢ (connectedComponentIn (F ⁻¹' {F x}) x)) {N : Set (ι → ℝ)} (hN : N ∈ 𝓝 (F x)) :
    ∃ (V : Set M) (D : Set (ι → ℝ)), IsOpen V ∧ IsOpen D ∧
      connectedComponentIn (F ⁻¹' {F x}) x ⊆ V ∧ V ⊆ W ∧ D ⊆ N ∧ F '' V = D ∧
      (∀ y ∈ V, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y) ∧
      (∀ y ∈ V, V ∩ F ⁻¹' {F y} = connectedComponentIn (F ⁻¹' {F y}) y) ∧
      ∀ K ⊆ D, IsCompact K → IsCompact (V ∩ F ⁻¹' K) := by
  obtain ⟨Ψ, A, U, hU, hxU, -, hrange, hΨ⟩ :=
    hσ.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact hF hcomm hdim hreg hK
  -- Over values near `F x`, the angles in the compact cube `[0, 2π]^ι` are sent into `W`.
  have hev : ∀ᶠ c in 𝓝 (F x), ∀ θ ∈ Icc (0 : ι → ℝ) (fun _ ↦ 2 * π), Ψ (θ, c) ∈ W := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun θ _ ↦ ?_
    have hcont : ContinuousAt (Ψ ∘ Prod.swap) (F x, θ) :=
      ContinuousAt.comp (f := Prod.swap) ((hΨ (F x) hxU).2.1 θ).contMDiffAt.continuousAt
        continuous_swap.continuousAt
    exact hcont.preimage_mem_nhds (mem_nhdsSet_iff_forall.1 hW _ (hrange ▸ mem_range_self θ))
  obtain ⟨D, hDsub, hDo, hxD⟩ := mem_nhds_iff.1 (hev.and (inter_mem hN (hU.mem_nhds hxU)))
  have hDU (c : ι → ℝ) (hc : c ∈ D) : c ∈ U := (hDsub hc).2.2
  have hper (c : ι → ℝ) (hc : c ∈ D) (θ : ι → ℝ) (m : ι → ℤ) :
      Ψ (θ + fun i ↦ 2 * π * m i, c) = Ψ (θ, c) :=
    (((hΨ c (hDU c hc)).2.2.2 c (hDU c hc) θ _).2 ⟨rfl, m, rfl⟩).symm
  obtain ⟨hVo, hFV, hregV, hfib, hcompact⟩ := image_univ_prod_saturated hF hDo
    (fun c hc ↦ (hΨ c (hDU c hc)).1) (fun c hc ↦ (hΨ c (hDU c hc)).2.1) hper
  refine ⟨_, D, hVo, hDo, ?_, ?_, fun c hc ↦ (hDsub hc).2.1, hFV, hregV, hfib, hcompact⟩
  · rw [← hrange]
    rintro _ ⟨θ, rfl⟩
    exact ⟨(θ, F x), ⟨trivial, hxD⟩, rfl⟩
  · -- each point of `V` is already the image of an angle in the cube
    rintro _ ⟨⟨θ, c⟩, ⟨-, hc⟩, rfl⟩
    have hmem : Ψ (θ, c) ∈ Ψ '' (univ ×ˢ {c}) := mem_image_of_mem _ ⟨trivial, rfl⟩
    rw [image_univ_prod_eq_image_Icc_prod hper (singleton_subset_iff.2 hc)] at hmem
    obtain ⟨⟨θ', c'⟩, ⟨hθ', hc'⟩, hΨθ⟩ := hmem
    rw [mem_singleton_iff] at hc'
    subst hc'
    exact hΨθ ▸ (hDsub hc).1 θ' hθ'

/-- **Complete Hamiltonian flows on a saturated neighbourhood of a compact regular Liouville
torus.** In the setting of `exists_inter_preimage_singleton_eq_connectedComponentIn`, the
compact regular component `L` has arbitrarily small saturated open neighbourhoods `V` on which the
Hamiltonian vector field of every `C²` function Poisson-commuting with the `F_i` is complete, as a
vector field on the open submanifold `V` with the restriction of `σ`. Since its flow preserves the
levels of `F` and the components of the levels in `V`, it preserves each of these compact
components. -/
theorem exists_opens_isCompleteVectorField_hamiltonianVectorField_of_isCompact
    (hσ : σ.IsSymplectic) (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
    (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) {W : Set M}
    (hW : W ∈ 𝓝ˢ (connectedComponentIn (F ⁻¹' {F x}) x)) :
    ∃ V : Opens M, connectedComponentIn (F ⁻¹' {F x}) x ⊆ V ∧ (V : Set M) ⊆ W ∧
      (∀ y ∈ V, (V : Set M) ∩ F ⁻¹' {F y} = connectedComponentIn (F ⁻¹' {F y}) y) ∧
      ∀ {f : M → ℝ}, ContMDiffOn I 𝓘(ℝ) 2 f V →
        (∀ y ∈ V, ∀ i, σ.poissonBracket (F · i) f y = 0) →
        IsCompleteVectorField (SmoothTwoForm.hamiltonianVectorField
          (SmoothForm.mpullback (Subtype.val : V → M) contMDiff_subtypeVal σ)
          fun y : V ↦ f y) := by
  obtain ⟨V, D, hV, -, hLV, hVW, -, hFV, -, hfib, hcompact⟩ :=
    hσ.exists_inter_preimage_singleton_eq_connectedComponentIn hF hcomm hdim hreg hK hW univ_mem
  -- every level of `F` meets `V` in a compact set, empty for values outside `D = F(V)`
  have hlev (c : ι → ℝ) : IsCompact (V ∩ F ⁻¹' {c}) := by
    by_cases hc : c ∈ D
    · exact hcompact _ (singleton_subset_iff.2 hc) isCompact_singleton
    · convert isCompact_empty
      exact eq_empty_of_forall_notMem fun y ⟨hy, hyc⟩ ↦ hc (hFV ▸ ⟨y, hy, hyc⟩)
  have hσ' := hσ.isNondegenerate
  exact ⟨⟨V, hV⟩, hLV, hVW, hfib, fun hf hfF ↦
    hσ'.isCompleteVectorField_hamiltonianVectorField_of_isCompact_inter_preimage_singleton
      (fun i ↦ ((contMDiff_pi_module_iff.1 hF i).mdifferentiable (by simp)).mdifferentiableOn)
      hlev hf hfF⟩

end IsSymplectic

namespace IsIntegrableSystem

/-- **Functions in involution with an integrable system near a compact regular Liouville torus.**
For an integrable system `F` for a symplectic form, let the connected component `L` of `x` in its
level `F⁻¹(F x)` be compact and consist of regular points. Then `L` has arbitrarily small open
neighbourhoods `V` on which every `C^n` function `f`, with `0 < n ≤ ∞`, that Poisson-commutes on
`V` with every `F_i` is `ψ ∘ F` for a single function `ψ`, which is `C^n` at every value of `F` on
`V`. -/
theorem exists_eqOn_comp_of_isCompact (h : σ.IsIntegrableSystem F) (hσ : σ.IsSymplectic) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) {W : Set M}
    (hW : W ∈ 𝓝ˢ (connectedComponentIn (F ⁻¹' {F x}) x)) :
    ∃ V : Set M, IsOpen V ∧ connectedComponentIn (F ⁻¹' {F x}) x ⊆ V ∧ V ⊆ W ∧
      ∀ {n : ℕ∞ω} {f : M → ℝ}, n ≠ 0 → n ≤ ∞ → ContMDiffOn I 𝓘(ℝ) n f V →
        (∀ y ∈ V, ∀ i, σ.poissonBracket (F · i) f y = 0) →
        ∃ ψ : (ι → ℝ) → ℝ, EqOn f (ψ ∘ F) V ∧ ∀ y ∈ V, ContDiffAt ℝ n ψ (F y) := by
  obtain ⟨V, -, hV, -, hLV, hVW, -, -, hregV, hfib, -⟩ :=
    hσ.exists_inter_preimage_singleton_eq_connectedComponentIn h.contMDiff
      h.poissonBracket_eq_zero h.two_mul_card_eq_finrank hreg hK hW univ_mem
  refine ⟨V, hV, hLV, hVW, fun hn hn' hf hfF ↦
    h.exists_eqOn_comp hσ.isNondegenerate hV hregV hn hn' hf hfF fun c ↦ ?_⟩
  -- each fibre `V ∩ F⁻¹(c)` is empty or a connected component of a level
  rcases (V ∩ F ⁻¹' {c}).eq_empty_or_nonempty with hc | ⟨y, hyV, rfl⟩
  · exact hc ▸ isPreconnected_empty
  · exact hfib y hyV ▸ isPreconnected_connectedComponentIn

end IsIntegrableSystem

end SmoothTwoForm

end TauCeti
