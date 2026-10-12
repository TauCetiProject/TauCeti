/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Shrinking
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Radial.Variable
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

/-!
# Assembling smooth tubular inverses

If normal addition is a local diffeomorphism along the zero section of a Euclidean normal
bundle, it identifies a sufficiently small variable-radius tube smoothly with an open
neighbourhood of the embedded image. Radial compression then identifies the entire normal
bundle with that neighbourhood. Both directions are smooth, and the neighbourhood can be
chosen inside any prescribed open neighbourhood of the image.

These are global assembly theorems: local invertibility of normal addition at zero vectors
is an explicit input, not a conclusion. They provide smooth normal coordinates on arbitrarily
small ambient neighbourhoods, either from a variable-radius tube or from the whole normal bundle.

The source must be nonempty because a `PartialDiffeomorph` has an inverse defined everywhere,
including outside its target. No compactness or properness of the embedding is needed.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public section

noncomputable section

open Set Function Bundle Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {V E F H M : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [Nonempty M] {f : M → V}

/-- Local invertibility of normal addition along the zero section upgrades a sufficiently
small smooth tubular radius to a partial diffeomorphism. Its source is exactly the open
normal ball bundle and its target lies in the prescribed ambient neighbourhood. -/
theorem exists_partialDiffeomorph_normalBundle_add_subset
    (hf : ContMDiff I 𝓘(ℝ, V) 2 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hind : IsInducing f)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    (hlocal :
      letI := normalFiberBundle (hf.of_le (by simp)) himm hdim
      ∀ x, IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) ∞
        (fun p : TotalSpace F (fun x => normalSubspace I f x) => f p.proj + p.2)
        (zeroSection F (fun x => normalSubspace I f x) x))
    {O : Set V} (hO : IsOpen O) (hfO : range f ⊆ O) :
    letI := normalFiberBundle (hf.of_le (by simp)) himm hdim
    ∃ r : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ x, 0 < r x) ∧
      ∃ Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V)
          (TotalSpace F (fun x => normalSubspace I f x)) V ∞,
        Φ.source = {p | ‖(p.2 : V)‖ < r p.proj} ∧ Φ.target ⊆ O ∧
          ∀ p, Φ p = f p.proj + p.2 := by
  let := normalFiberBundle (hf.of_le (by simp)) himm hdim
  have : SecondCountableTopology M := hind.secondCountableTopology
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let a : TotalSpace F (fun x => normalSubspace I f x) → V :=
    fun p => f p.proj + p.2
  let U := {p | IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) ∞ a p}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun _ hp => hp.eventually
  obtain ⟨r, hr, hemb, hambient, hdisc⟩ :=
    exists_isOpenEmbedding_normalTubeOfRadius_contMDiff_subset_zeroSection
      hf himm hind hU hlocal hO hfO
  let S := {p : TotalSpace F (fun x => normalSubspace I f x) | ‖(p.2 : V)‖ < r p.proj}
  have hS : IsOpen S := by
    have he := (isEmbedding_totalSpace_normalSubspace (I := I) (F := F) f).continuous
    exact isOpen_lt (continuous_norm.comp he.snd) (r.contMDiff.continuous.comp he.fst)
  have ha : IsLocalDiffeomorphOn (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) ∞ a S :=
    fun p => hdisc p.1 p.2.le
  have hinj : InjOn a S := by
    intro p hp q hq hpq
    apply (isEmbedding_totalSpace_normalSubspace (F := F) f).injective
    exact congrArg Subtype.val (hemb.injective
      (a₁ := ⟨(p.proj, (p.2 : V)), mem_normalTubeOfRadius.mpr ⟨p.2.2, hp⟩⟩)
      (a₂ := ⟨(q.proj, (q.2 : V)), mem_normalTubeOfRadius.mpr ⟨q.2.2, hq⟩⟩) hpq)
  have : Nonempty (TotalSpace F (fun x => normalSubspace I f x)) :=
    Nonempty.map (zeroSection F (fun x => normalSubspace I f x)) inferInstance
  let Φ := ha.partialDiffeomorphOfInjOn hS hinj
  refine ⟨r, hr, Φ, ha.partialDiffeomorphOfInjOn_source hS hinj, ?_, ?_⟩
  · rw [IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target]
    rintro _ ⟨p, hp, rfl⟩
    exact hambient p.proj p.2 hp.le
  · intro p
    rw [IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn]

/-- Radial compression and local invertibility along the zero section give a smooth
identification of the whole normal bundle with an open ambient neighbourhood. The map
has the explicit compressed-normal-vector formula and fixes the embedded core. -/
theorem exists_partialDiffeomorph_wholeNormalBundle_subset
    (hf : ContMDiff I 𝓘(ℝ, V) ∞ f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hind : IsInducing f)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    (hlocal :
      letI := normalFiberBundle (hf.of_le (by simp)) himm hdim
      ∀ x, IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) ∞
        (fun p : TotalSpace F (fun x => normalSubspace I f x) => f p.proj + p.2)
        (zeroSection F (fun x => normalSubspace I f x) x))
    {O : Set V} (hO : IsOpen O) (hfO : range f ⊆ O) :
    letI := normalFiberBundle (hf.of_le (by simp)) himm hdim
    ∃ r : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ x, 0 < r x) ∧
      ∃ Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V)
          (TotalSpace F (fun x => normalSubspace I f x)) V ∞,
        Φ.source = univ ∧ Φ.target ⊆ O ∧
          (∀ p, Φ p = f p.proj +
            r p.proj • OpenPartialHomeomorph.univUnitBall (p.2 : V)) ∧
          ∀ x, Φ (zeroSection F (fun x => normalSubspace I f x) x) = f x := by
  let := normalFiberBundle (hf.of_le (by simp)) himm hdim
  obtain ⟨r, hr, Ψ, hsource, htarget, hΨ⟩ :=
    exists_partialDiffeomorph_normalBundle_add_subset
      (hf.of_le (by simp)) himm hind hdim hlocal hO hfO
  have hf' : ContMDiff I 𝓘(ℝ, V) (↑(⊤ : ℕ∞) + 1) f := by simpa using hf
  have : IsManifold I (↑(⊤ : ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  let R := normalBundleRadialPartialDiffeomorphOfRadius hf' himm hdim r.contMDiff hr
  have hRsource : R.source = univ :=
    normalBundleRadialPartialDiffeomorphOfRadius_source hf' himm hdim r.contMDiff hr
  have hRtarget : R.target = Ψ.source := by
    rw [normalBundleRadialPartialDiffeomorphOfRadius_target, hsource]
  have hcomp_source : (R.trans Ψ).source = univ := by
    have hpreimage : R ⁻¹' Ψ.source = univ :=
      eq_univ_of_forall fun p => hRtarget ▸ R.map_source (hRsource ▸ mem_univ p)
    simp [hRsource, hpreimage]
  have hformula (p : TotalSpace F (fun x => normalSubspace I f x)) :
      (R.trans Ψ) p = f p.proj +
        r p.proj • OpenPartialHomeomorph.univUnitBall (p.2 : V) := by
    simp [hΨ, R, normalBundleRadialPartialDiffeomorphOfRadius_apply]
  refine ⟨r, hr, R.trans Ψ, hcomp_source, ?_, hformula, ?_⟩
  · exact fun p hp => htarget hp.1
  · intro x
    rw [hformula]
    simp [zeroSection]

end TauCeti
