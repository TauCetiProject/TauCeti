/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.DoubleDual.Line
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial
import Mathlib.RingTheory.SimpleModule.Rank
import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Nowhere-vanishing sections of a line bundle and of its dual

Let `V` be a vector bundle of rank one over a manifold `B`, and let `V* = Hom(V, B × 𝕜)` be its
dual line bundle, with fibres `V x →L[𝕜] 𝕜`. A nowhere-vanishing `C^n` section of either bundle
gives one of the other, normalized against it:

* a `C^n` section `f` of `V*` vanishing nowhere has a `C^n` dual section `s` of `V`, with
  `f x (s x) = 1` at every point (`TauCeti.exists_contMDiff_section_apply_eq_one`): each `f x` is
  an isomorphism of the line `V x` onto `𝕜`, these isomorphisms form a `C^n` family, so their
  inverses do too, and `s` is the inverse image of the constant section `1`;
* a `C^n` section `s` of `V` vanishing nowhere has a `C^n` dual section `f` of `V*`, with
  `f x (s x) = 1` (`TauCeti.exists_contMDiff_dual_section_apply_eq_one`): read `s` as a section of
  the double dual `V**` (`TauCeti.bundleLineDoubleDualDiffeomorph`) and apply the first statement
  to the line bundle `V*`.

So `V` has a nowhere-vanishing `C^n` section exactly when `V*` has one
(`TauCeti.exists_contMDiff_section_ne_zero_iff_dual`). Since a `C^n` line bundle is trivial exactly
when it has a nowhere-vanishing `C^n` section
(`ContMDiffVectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero`), a `C^n` line
bundle is `C^n`-trivial exactly when its dual is
(`TauCeti.exists_trivialization_baseSet_eq_univ_iff_dual`). For the contact line `L` of a contact
structure `ξ`, whose dual is the annihilator line `ξ⁰`, this is the step from the triviality of
`ξ⁰`, that is the existence of a global contact form, to the triviality of `L`.
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {n : ℕ∞ω}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]

attribute [local instance] Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
  Bundle.ContinuousLinearMap.fiberBundle Bundle.ContinuousLinearMap.vectorBundle

/-- **A nowhere-vanishing section of the dual of a line bundle has a dual section.** For a vector
bundle `V` of rank one and a `C^n` section `f` of its dual `V*` vanishing nowhere, there is a
`C^n` section `s` of `V` with `f x (s x) = 1` at every point. -/
theorem exists_contMDiff_section_apply_eq_one (hF : finrank 𝕜 F = 1) {f : Π x, V x →L[𝕜] 𝕜}
    (hf : ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun x ↦ V x →L[𝕜] Trivial B 𝕜 x) x (f x)))
    (hf₀ : ∀ x, f x ≠ 0) :
    ∃ s : Π x, V x, ContMDiff IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) ∧
      ∀ x, f x (s x) = 1 := by
  have : FiniteDimensional 𝕜 F := Module.finite_of_finrank_eq_succ hF
  -- On the line `V x`, the nonzero functional `f x` is an isomorphism onto `𝕜`.
  have h (x : B) : ∃ e : V x ≃L[𝕜] Trivial B 𝕜 x, ⇑e = f x := by
    have := VectorBundle.isTopologicalAddGroup 𝕜 F V x
    have := VectorBundle.continuousSMul 𝕜 F V x
    let := FiberBundle.t2Space F V x
    let := VectorBundle.finiteDimensional 𝕜 F V x
    have : IsSimpleModule 𝕜 (V x) := isSimpleModule_iff_finrank_eq_one.2 <| by
      rw [((trivializationAt F V x).continuousLinearEquivAt 𝕜 x
        (mem_baseSet_trivializationAt F V x)).toLinearEquiv.finrank_eq, hF]
    have hbij : Function.Bijective (f x) := LinearMap.bijective_of_ne_zero (N := 𝕜)
      (f := (f x).toLinearMap) (ContinuousLinearMap.coe_injective.ne (hf₀ x))
    exact ⟨(LinearEquiv.ofBijective (f x).toLinearMap hbij).toContinuousLinearEquiv, rfl⟩
  choose e he using h
  have hcont : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, 𝕜)) n
      (fun p : TotalSpace F V ↦ TotalSpace.mk' 𝕜 (E := Trivial B 𝕜) p.proj (e p.proj p.snd)) := by
    simpa only [he] using (contMDiff_hom_bundle_iff f).1 hf
  -- The inverse isomorphisms are `C^n` as well; apply them to the constant section `1`.
  refine ⟨fun x ↦ (e x).symm 1,
    (contMDiff_bundle_symm e hcont).comp (Trivial.contMDiff_mk_const 1), fun x ↦ ?_⟩
  rw [← he x]
  exact (e x).apply_symm_apply 1

/-- **A nowhere-vanishing section of a line bundle has a dual section.** For a vector bundle `V` of
rank one and a `C^n` section `s` of `V` vanishing nowhere, there is a `C^n` section `f` of the dual
line bundle `V*` with `f x (s x) = 1` at every point. -/
theorem exists_contMDiff_dual_section_apply_eq_one (hF : finrank 𝕜 F = 1) {s : Π x, V x}
    (hs : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)))
    (hs₀ : ∀ x, s x ≠ 0) :
    ∃ f : Π x, V x →L[𝕜] 𝕜, ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun x ↦ V x →L[𝕜] Trivial B 𝕜 x) x (f x)) ∧
      ∀ x, f x (s x) = 1 := by
  have : FiniteDimensional 𝕜 F := Module.finite_of_finrank_eq_succ hF
  have hF' : finrank 𝕜 (F →L[𝕜] 𝕜) = 1 := ContinuousLinearMap.dual_finrank_eq.trans hF
  -- Read `s` as a nowhere-vanishing section of the double dual, the dual of the line `V*`.
  have ht := (bundleLineDoubleDualDiffeomorph (F := F) V (Trivial B 𝕜) (I := IB) (n := n)
    ).contMDiff.comp hs
  obtain ⟨f, hf, hfs⟩ := exists_contMDiff_section_apply_eq_one
    (V := fun x ↦ V x →L[𝕜] Trivial B 𝕜 x) hF'
    (f := fun x ↦ bundleLineDoubleDualEquiv (F := F) V (Trivial B 𝕜) x (s x))
    (by simpa [Function.comp_def] using ht) fun x ↦ by simpa using hs₀ x
  exact ⟨f, hf, fun x ↦ by simpa using hfs x⟩

/-- **A line bundle has a nowhere-vanishing section exactly when its dual does.** For a vector
bundle `V` of rank one, `V` has a `C^n` section vanishing nowhere exactly when its dual line
bundle `V*` has one. -/
theorem exists_contMDiff_section_ne_zero_iff_dual (hF : finrank 𝕜 F = 1) :
    (∃ s : Π x, V x, ContMDiff IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) ∧
      ∀ x, s x ≠ 0) ↔
    ∃ f : Π x, V x →L[𝕜] 𝕜, ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun x ↦ V x →L[𝕜] Trivial B 𝕜 x) x (f x)) ∧
      ∀ x, f x ≠ 0 := by
  constructor
  · rintro ⟨s, hs, hs₀⟩
    obtain ⟨f, hf, hfs⟩ := exists_contMDiff_dual_section_apply_eq_one hF hs hs₀
    exact ⟨f, hf, fun x h ↦ by simpa [h] using hfs x⟩
  · rintro ⟨f, hf, hf₀⟩
    obtain ⟨s, hs, hfs⟩ := exists_contMDiff_section_apply_eq_one hF hf hf₀
    exact ⟨s, hs, fun x h ↦ by simpa [h] using hfs x⟩

/-- **A line bundle is trivial exactly when its dual is.** A `C^n` vector bundle `V` of rank one
has a `C^n` linear trivialization over all of `B` exactly when its dual line bundle `V*` has
one. -/
theorem exists_trivialization_baseSet_eq_univ_iff_dual [ContMDiffVectorBundle n F V IB]
    (hF : finrank 𝕜 F = 1) :
    (∃ (e : Trivialization F (π F V)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F V) ∧
        e.baseSet = Set.univ) ↔
      ∃ (e : Trivialization (F →L[𝕜] 𝕜) (π (F →L[𝕜] 𝕜) fun x ↦ V x →L[𝕜] Trivial B 𝕜 x))
          (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈ (contMDiffFiberwiseLinear B (F →L[𝕜] 𝕜) IB n).maximalAtlas
          (TotalSpace (F →L[𝕜] 𝕜) fun x ↦ V x →L[𝕜] Trivial B 𝕜 x) ∧
        e.baseSet = Set.univ := by
  have : FiniteDimensional 𝕜 F := Module.finite_of_finrank_eq_succ hF
  rw [ContMDiffVectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero hF,
    ContMDiffVectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero
      (ContinuousLinearMap.dual_finrank_eq.trans hF)]
  exact exists_contMDiff_section_ne_zero_iff_dual hF

end TauCeti
