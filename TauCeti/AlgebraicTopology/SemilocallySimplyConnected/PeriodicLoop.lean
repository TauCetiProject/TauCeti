/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.On
public import TauCeti.Topology.Homotopy.AddCircle

/-!
# Null-homotopy of periodic loops in semilocally simply connected spaces

In a locally path-connected, semilocally simply connected space `X`, null-homotopy of based loops is
a clopen property in any continuous family (`TauCeti.isClopen_setOf_homotopic_refl`). Combined with
the correspondence `Function.Periodic.exists_nullhomotopic_iff_loop_homotopic_refl` between free
circle null-homotopy on `AddCircle T` (`0 < T`) and based-loop null-homotopy over one period, this
yields invariance of circle contractibility under continuous deformations and uniform limits of
periodic curves.

When `K ⊆ X` is compact and `e : X → F` is a continuous map into a Hausdorff uniform space that is
injective on `K`, `e` restricts to a closed embedding `K → F`. Uniform convergence of `e ∘ γ_i` in
`F` therefore lifts to uniform—hence continuous—convergence of the periodic curves `γ_i` in `K`, so
null-homotopy of the induced circle maps `AddCircle T → X` is preserved along the limit.

## Main results

* `TauCeti.exists_nullhomotopic_slice_iff_of_isPreconnected`: null-homotopy of `T`-periodic slices
  `u(p, ·)` is constant along preconnected parameter sets `U`.
* `TauCeti.isClopen_setOf_exists_nullhomotopic_of_isCompact`: inside the uniform-convergence space
  of continuous `T`-periodic curves in `e '' K`, those lifting to a null-homotopic circle map in `K`
  form a clopen subset.
* `TauCeti.eventually_exists_nullhomotopic_iff_of_tendstoUniformly_comp`: uniform convergence
  through an injective map on a compact set eventually preserves circle null-homotopy of periodic
  curves.
-/

public section

open Filter Function Set Topology
open scoped UniformConvergence unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] {T : ℝ}

/-- **Null-homotopy of periodic slices is constant along preconnected parameter sets.** Let `X` be a
locally path-connected, semilocally simply connected space, `U` a preconnected subset of a
topological space `P`, and `u : P × ℝ → X` continuous on `U × ℝ` with `T`-periodic slices (`0 < T`).
Then the circle map `AddCircle T → X` of `u(p₁, ·)` is null-homotopic if and only if that of
`u(p₂, ·)` is, for any `p₁, p₂ ∈ U`. -/
theorem exists_nullhomotopic_slice_iff_of_isPreconnected {P : Type*} [TopologicalSpace P]
    {U : Set P} (hU : IsPreconnected U) {u : P × ℝ → X} (hu : ContinuousOn u (U ×ˢ univ))
    (hT : 0 < T) (hper : ∀ p ∈ U, Periodic (fun t ↦ u (p, t)) T) {p₁ p₂ : P} (hp₁ : p₁ ∈ U)
    (hp₂ : p₂ ∈ U) :
    (∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (p₁, t)) ↔
      ∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (p₂, t) := by
  have : Fact (0 < T) := ⟨hT⟩
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.1 hU
  have hslice (p : U) : Continuous fun t ↦ u (p.1, t) :=
    hu.comp_continuous (continuous_const.prodMk continuous_id) fun t ↦ ⟨p.2, mem_univ t⟩
  let γ (p : U) : Path (u (p.1, 0)) (u (p.1, 0)) := (hper p.1 p.2).loop (hslice p) 0
  have hγ_eq : ↿γ = fun q : U × I ↦ u (q.1.1, (0 : ℝ) + (q.2 : ℝ) * T) :=
    funext fun q ↦ (hper q.1.1 q.1.2).loop_apply (hslice q.1) 0 q.2
  have hγ : Continuous ↿γ := by
    rw [hγ_eq]
    exact hu.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_const.add ((continuous_subtype_val.comp continuous_snd).mul continuous_const)))
      fun q ↦ ⟨q.1.2, mem_univ _⟩
  have hclopen := isClopen_setOf_homotopic_refl γ hγ
  rw [(hper p₁ hp₁).exists_nullhomotopic_iff_loop_homotopic_refl (hslice ⟨p₁, hp₁⟩) 0,
    (hper p₂ hp₂).exists_nullhomotopic_iff_loop_homotopic_refl (hslice ⟨p₂, hp₂⟩) 0]
  rcases isClopen_iff.1 hclopen with h | h
  · have h₁ : (⟨p₁, hp₁⟩ : U) ∉ {p : U | (γ p).Homotopic (Path.refl (u (p.1, 0)))} :=
      h ▸ notMem_empty _
    have h₂ : (⟨p₂, hp₂⟩ : U) ∉ {p : U | (γ p).Homotopic (Path.refl (u (p.1, 0)))} :=
      h ▸ notMem_empty _
    exact iff_of_false h₁ h₂
  · have h₁ : (⟨p₁, hp₁⟩ : U) ∈ {p : U | (γ p).Homotopic (Path.refl (u (p.1, 0)))} :=
      h.symm ▸ mem_univ _
    have h₂ : (⟨p₂, hp₂⟩ : U) ∈ {p : U | (γ p).Homotopic (Path.refl (u (p.1, 0)))} :=
      h.symm ▸ mem_univ _
    exact iff_of_true h₁ h₂

/-- **Null-homotopic periodic lifts form a clopen set in the topology of uniform convergence.**
Inside the space of continuous `T`-periodic curves (`0 < T`) in `e '' K` equipped with the topology
of uniform convergence, where `K ⊆ X` is compact and `e : X → F` is continuous and injective on `K`
into a Hausdorff uniform space `F`, those whose unique lift in `K` descends to a null-homotopic map
`AddCircle T → X` form a clopen subset. -/
theorem isClopen_setOf_exists_nullhomotopic_of_isCompact {F : Type*} [UniformSpace F] [T2Space F]
    {e : X → F} {K : Set X} (hK : IsCompact K) (he : ContinuousOn e K) (he_inj : InjOn e K)
    (hT : 0 < T) :
    IsClopen {f : {f : ℝ →ᵤ F | Continuous (UniformFun.toFun f) ∧
        Periodic (UniformFun.toFun f) T ∧ ∀ t, UniformFun.toFun f t ∈ e '' K} |
      ∃ γ : ℝ → X, (∀ t, γ t ∈ K) ∧ e ∘ γ = UniformFun.toFun f.1 ∧
        ∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t} := by
  have : Fact (0 < T) := ⟨hT⟩
  have := isCompact_iff_compactSpace.1 hK
  -- On the compact domain `K`, `e` restricts to a closed embedding, giving a continuous inverse.
  have hemb : IsClosedEmbedding fun p : K ↦ e p :=
    (he.comp_continuous continuous_subtype_val Subtype.prop).isClosedEmbedding fun p q h ↦
      Subtype.ext (he_inj p.2 q.2 h)
  let φ : range (fun p : K ↦ e p) ≃ₜ K := hemb.isEmbedding.toHomeomorph.symm
  let L := {f : ℝ →ᵤ F | Continuous (UniformFun.toFun f) ∧ Periodic (UniformFun.toFun f) T ∧
    ∀ t, UniformFun.toFun f t ∈ e '' K}
  have hmem (f : L) (t : ℝ) : UniformFun.toFun f.1 t ∈ range fun p : K ↦ e p := by
    obtain ⟨p, hp, hp'⟩ := f.2.2.2 t
    exact ⟨⟨p, hp⟩, hp'⟩
  let lift (f : L) (t : ℝ) : X := (φ ⟨UniformFun.toFun f.1 t, hmem f t⟩ : K)
  have hliftK (f : L) (t : ℝ) : lift f t ∈ K := (φ _).2
  have helift (f : L) : e ∘ lift f = UniformFun.toFun f.1 := funext fun t ↦
    congrArg Subtype.val
      (hemb.isEmbedding.toHomeomorph.apply_symm_apply ⟨UniformFun.toFun f.1 t, hmem f t⟩)
  have hliftc (f : L) : Continuous (lift f) :=
    continuous_subtype_val.comp (φ.continuous.comp (f.2.1.subtype_mk (hmem f)))
  have hliftp (f : L) : Periodic (lift f) T := fun t ↦ by
    dsimp only [lift]
    congr 2
    exact Subtype.ext (f.2.2.1 t)
  -- Joint continuity of evaluation follows from uniform convergence and continuity of each curve.
  have hθc : Continuous fun θ : I ↦ (0 : ℝ) + (θ : ℝ) * T :=
    continuous_const.add ((continuous_subtype_val.comp continuous_id).mul continuous_const)
  have heval : Continuous fun q : L × I ↦ UniformFun.toFun q.1.1 ((0 : ℝ) + (q.2 : ℝ) * T) :=
    continuous_iff_continuousAt.2 fun q₀ ↦
      (UniformFun.tendsto_iff_tendstoUniformly.1
        (continuous_subtype_val.comp continuous_fst).continuousAt).tendsto_comp
        q₀.1.2.1.continuousAt (hθc.comp continuous_snd).continuousAt
  have hfam_eq : (↿fun f : L ↦ (hliftp f).loop (hliftc f) 0) =
      fun q : L × I ↦ lift q.1 ((0 : ℝ) + (q.2 : ℝ) * T) :=
    funext fun q ↦ (hliftp q.1).loop_apply (hliftc q.1) 0 q.2
  have hfam : Continuous ↿fun f : L ↦ (hliftp f).loop (hliftc f) 0 := by
    rw [hfam_eq]
    exact continuous_subtype_val.comp
      (φ.continuous.comp (heval.subtype_mk fun q ↦ hmem q.1 ((0 : ℝ) + (q.2 : ℝ) * T)))
  have hset : {f : L | ∃ γ : ℝ → X, (∀ t, γ t ∈ K) ∧ e ∘ γ = UniformFun.toFun f.1 ∧
        ∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t} =
      {f : L | ((hliftp f).loop (hliftc f) 0).Homotopic (Path.refl (lift f 0))} := by
    ext f
    simp only [mem_ofPred_eq,
      ← (hliftp f).exists_nullhomotopic_iff_loop_homotopic_refl (hliftc f) 0]
    refine ⟨?_, fun h ↦ ⟨lift f, hliftK f, helift f, h⟩⟩
    rintro ⟨γ, hγK, heγ, hnull⟩
    have hγeq : γ = lift f := funext fun t ↦
      he_inj (hγK t) (hliftK f t) (congrFun (heγ.trans (helift f).symm) t)
    exact hγeq ▸ hnull
  rw [hset]
  exact isClopen_setOf_homotopic_refl (fun f : L ↦ (hliftp f).loop (hliftc f) 0) hfam

/-- **Uniform convergence through an injective map on a compact set eventually preserves loop
contractibility.** Let `X` be a locally path-connected, semilocally simply connected space, `K ⊆ X`
compact, and `e : X → F` continuous and injective on `K` into a Hausdorff uniform space `F`. If
eventually continuous `T`-periodic curves `γ_i` in `K` (`0 < T`) converge uniformly after applying
`e` to `e ∘ γ₀` for a continuous `T`-periodic curve `γ₀` in `K`, then eventually `γ_i` is
null-homotopic as a map `AddCircle T → X` if and only if `γ₀` is. -/
theorem eventually_exists_nullhomotopic_iff_of_tendstoUniformly_comp {F : Type*} [UniformSpace F]
    [T2Space F] {e : X → F} {K : Set X} (hK : IsCompact K) (he : ContinuousOn e K)
    (he_inj : InjOn e K) (hT : 0 < T) {ι : Type*} {l : Filter ι} {γ : ι → ℝ → X} {γ₀ : ℝ → X}
    (hγ₀c : Continuous γ₀) (hγ₀p : Periodic γ₀ T) (hγ₀K : ∀ t, γ₀ t ∈ K)
    (hγc : ∀ᶠ i in l, Continuous (γ i)) (hγp : ∀ᶠ i in l, Periodic (γ i) T)
    (hγK : ∀ᶠ i in l, ∀ t, γ i t ∈ K) (hconv : TendstoUniformly (fun i t ↦ e (γ i t)) (e ∘ γ₀) l) :
    ∀ᶠ i in l, (∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ i t) ↔
      ∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ₀ t := by
  let L := {f : ℝ →ᵤ F | Continuous (UniformFun.toFun f) ∧ Periodic (UniformFun.toFun f) T ∧
    ∀ t, UniformFun.toFun f t ∈ e '' K}
  let P : Set L := {f | ∃ γ' : ℝ → X, (∀ t, γ' t ∈ K) ∧ e ∘ γ' = UniformFun.toFun f.1 ∧
    ∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ' t}
  have hclopen : IsClopen P := isClopen_setOf_exists_nullhomotopic_of_isCompact hK he he_inj hT
  have hmemP {δ : ℝ → X} (hδK : ∀ t, δ t ∈ K) (f : L) (hf : UniformFun.toFun f.1 = e ∘ δ) :
      f ∈ P ↔ ∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = δ t := by
    refine ⟨?_, fun h ↦ ⟨δ, hδK, hf.symm, h⟩⟩
    rintro ⟨γ', hγ'K, heγ', hnull⟩
    have heq : γ' = δ := funext fun t ↦
      he_inj (hγ'K t) (hδK t) (congrFun (heγ'.trans hf) t)
    exact heq ▸ hnull
  let f₀ : L := ⟨UniformFun.ofFun (e ∘ γ₀), he.comp_continuous hγ₀c hγ₀K,
    fun t ↦ by simp only [UniformFun.toFun_ofFun, comp_apply, hγ₀p t],
    fun t ↦ mem_image_of_mem e (hγ₀K t)⟩
  have hf₀P : f₀ ∈ P ↔ ∃ g : C(AddCircle T, X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ₀ t :=
    hmemP hγ₀K f₀ (UniformFun.toFun_ofFun _)
  have hlim : Tendsto (fun i ↦ UniformFun.ofFun fun t ↦ e (γ i t)) l (𝓝 f₀.1) :=
    UniformFun.tendsto_iff_tendstoUniformly.2 hconv
  by_cases hxP : f₀ ∈ P
  · obtain ⟨U, hU, hUP⟩ := (mem_nhds_subtype L f₀ P).1 (hclopen.isOpen.mem_nhds hxP)
    filter_upwards [hγc, hγp, hγK, hlim.eventually hU] with i hic hip hiK hiU
    let fi : L := ⟨UniformFun.ofFun (e ∘ γ i), he.comp_continuous hic hiK,
      fun t ↦ by simp only [UniformFun.toFun_ofFun, comp_apply, hip t],
      fun t ↦ mem_image_of_mem e (hiK t)⟩
    exact iff_of_true ((hmemP hiK fi (UniformFun.toFun_ofFun _)).1 (hUP hiU)) (hf₀P.1 hxP)
  · obtain ⟨U, hU, hUP⟩ := (mem_nhds_subtype L f₀ Pᶜ).1 (hclopen.compl.isOpen.mem_nhds hxP)
    filter_upwards [hγc, hγp, hγK, hlim.eventually hU] with i hic hip hiK hiU
    let fi : L := ⟨UniformFun.ofFun (e ∘ γ i), he.comp_continuous hic hiK,
      fun t ↦ by simp only [UniformFun.toFun_ofFun, comp_apply, hip t],
      fun t ↦ mem_image_of_mem e (hiK t)⟩
    exact iff_of_false
      (fun hi ↦ hUP hiU ((hmemP hiK fi (UniformFun.toFun_ofFun _)).2 hi))
      (fun hx' ↦ hxP (hf₀P.2 hx'))

end TauCeti
