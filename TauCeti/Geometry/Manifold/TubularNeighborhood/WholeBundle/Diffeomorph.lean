/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.LocalInverse
public import TauCeti.Geometry.Manifold.TubularNeighborhood.WholeBundle.GlobalInverse
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Diffeomorph

/-!
# Smooth tubular neighbourhoods of Euclidean embeddings

The whole normal bundle of a smooth Euclidean embedding is diffeomorphic to an open
neighbourhood of its image, with the zero section sent to the original embedding. The
neighbourhood may be chosen inside any prescribed open neighbourhood, even for noncompact
sources. Both the orthogonal normal bundle and the intrinsic quotient normal bundle are
supported.

The orthogonal construction combines local invertibility of normal addition with smooth
variable-radius compression. The intrinsic construction transports it along
`SmoothEmbedding.normalBundleDiffeomorphOrthogonal`. These coordinates supply smooth
tubular inverses, rather than only regularity of the forward parametrization.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. Hirsch, *Differential Topology*, Theorem 6.3.
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

/-- **Smooth Euclidean tubular neighbourhood theorem.** The whole orthogonal normal bundle
of a smooth immersion inducing the source topology is diffeomorphic to an open neighbourhood
of its image, inside any prescribed open neighbourhood. The identification fixes the core.
Neither compactness nor closedness of the image is required. -/
theorem exists_diffeomorph_wholeNormalBundle_subset {f : M → V}
    (hf : ContMDiff I 𝓘(ℝ, V) ∞ f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hind : IsInducing f)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set V} (hO : IsOpen O) (hfO : range f ⊆ O) :
    letI := normalFiberBundle (hf.of_le (by simp)) himm hdim
    ∃ W : TopologicalSpace.Opens V, (W : Set V) ⊆ O ∧
      ∃ Φ : TotalSpace F (fun x => normalSubspace I f x) ≃ₘ^∞⟮I.prod 𝓘(ℝ, F), 𝓘(ℝ, V)⟯ W,
        ∀ x, (Φ (zeroSection F (fun x => normalSubspace I f x) x) : V) = f x := by
  classical
  let := normalFiberBundle (hf.of_le (by simp)) himm hdim
  cases isEmpty_or_nonempty M with
  | inl hM =>
    let W : TopologicalSpace.Opens V := ⊥
    have : IsEmpty (TotalSpace F (fun x => normalSubspace I f x)) :=
      ⟨fun p => hM.false p.proj⟩
    have : IsEmpty W := ⟨fun y => y.property⟩
    let Φ : TotalSpace F (fun x => normalSubspace I f x) ≃ₘ^∞⟮I.prod 𝓘(ℝ, F), 𝓘(ℝ, V)⟯ W :=
      { Equiv.equivOfIsEmpty _ _ with
        contMDiff_toFun := fun p => (hM.false p.proj).elim
        contMDiff_invFun := fun y => (IsEmpty.false y).elim }
    exact ⟨W, empty_subset O, Φ, fun x => (hM.false x).elim⟩
  | inr hM =>
    let := hM
    have hf' : ContMDiff I 𝓘(ℝ, V) (∞ + 1) f := by simpa using hf
    have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
    have hlocal := fun x => isLocalDiffeomorphAt_normalBundle_add_zeroSection
      hf' himm hdim x (by simp : (1 : ℕ∞ω) ≤ ∞)
    obtain ⟨-, -, Ψ, hsource, htarget, -, hzero⟩ :=
      exists_partialDiffeomorph_wholeNormalBundle_subset hf himm hind hdim hlocal hO hfO
    have hforward : ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) ∞ Ψ := by
      rw [← contMDiffOn_univ, ← hsource]
      exact Ψ.contMDiffOn
    let W : TopologicalSpace.Opens V := ⟨Ψ.target, Ψ.open_target⟩
    let Φ : TotalSpace F (fun x => normalSubspace I f x) ≃ₘ^∞⟮I.prod 𝓘(ℝ, F), 𝓘(ℝ, V)⟯ W :=
      { toFun := fun p => ⟨Ψ p, Ψ.toPartialEquiv.map_source (hsource ▸ mem_univ p)⟩
        invFun := fun y => Ψ.toPartialEquiv.symm y
        left_inv := fun p => Ψ.toPartialEquiv.left_inv (hsource ▸ mem_univ p)
        right_inv := fun y => Subtype.ext (Ψ.toPartialEquiv.right_inv y.property)
        contMDiff_toFun := by
          apply (_root_.ContMDiff.subtypeVal_comp_iff W _).mp
          exact hforward
        contMDiff_invFun := Ψ.contMDiffOn_invFun.comp_contMDiff contMDiff_subtype_val
          (fun y => y.property) }
    exact ⟨W, htarget, Φ, hzero⟩

namespace SmoothEmbedding

/-- **Intrinsic smooth Euclidean tubular neighbourhood theorem.** The quotient normal bundle
of a smooth embedding is diffeomorphic to an open neighbourhood inside any prescribed open
neighbourhood of the image. Its zero section is identified with the given embedding. -/
theorem exists_diffeomorph_normalBundle_subset
    (f : SmoothEmbedding I 𝓘(ℝ, V) ∞ M V)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set V} (hO : IsOpen O) (hfO : range f ⊆ O) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle (F := F) hn hdim
    ∃ W : TopologicalSpace.Opens V, (W : Set V) ⊆ O ∧
      ∃ Φ : TotalSpace F (fun x => f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, F), 𝓘(ℝ, V)⟯ W,
        ∀ x, (Φ (zeroSection F (fun x => f.NormalSpace x hn) x) : V) = f x := by
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let := f.normalSpaceFiberBundle (F := F) hn hdim
  let := normalFiberBundle (f.contMDiff.of_le (by simp))
    (f.isImmersion.mfderiv_injective hn) hdim
  obtain ⟨W, hW, Φ, hzero⟩ := exists_diffeomorph_wholeNormalBundle_subset
    f.contMDiff (f.isImmersion.mfderiv_injective hn) f.isEmbedding.isInducing hdim hO hfO
  let e := f.normalBundleDiffeomorphOrthogonal hn hdim ∞
  refine ⟨W, hW, e.trans Φ, ?_⟩
  intro x
  simpa only [Diffeomorph.coe_trans, Function.comp_apply, e,
    normalBundleDiffeomorphOrthogonal_apply,
    zeroSection, map_zero] using hzero x

end SmoothEmbedding

end TauCeti
