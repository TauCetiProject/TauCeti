/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Slice
public import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# A Morse–Bott function along the fibres of a tubular neighbourhood

Let `i : S → M` be a critical submanifold of a function `f` on a boundaryless manifold, and let
`V → S` be a vector bundle with model fibre `P` whose rank is the codimension of `S`. Let
`Φ : V → M` be a map out of the total space which sends the zero section onto the submanifold,
`Φ (0_s) = i s`, and is a local diffeomorphism along the zero section, as the tubular
neighbourhood of `S` given by the normal bundle
(`TauCeti.SmoothEmbedding.exists_diffeomorph_normalBundle_subset`) is. This file reads `f` along
the fibres of `Φ`: over `s`, the **fibre slice**

`w ↦ f (Φ ⟨s, e.symm s w⟩)`, with `e = trivializationAt P V s`,

is a function on the model fibre `P`, the fibre of `f ∘ Φ` over `s` read in the preferred
trivialization at `s`.

The derivative of `Φ` at `0_s` restricts to the derivative of `i` on the tangent directions of
the zero section and is injective, so it carries the fibre directions isomorphically onto a
complement of the tangent space of the submanifold
(`TauCeti.SmoothEmbedding.bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm`). Each
fibre of `Φ` is therefore a transverse slice through the submanifold, and the results of
`TauCeti.Geometry.Manifold.Morse.Bott.Slice` apply: the fibre slice has a critical point at `0`,
whose Hessian is the normal Hessian read through the fibre derivative of `Φ`. When `i` is
Morse–Bott, this critical point is nondegenerate, and its Morse index is the Morse index of `f` at
`i s`.

So `f ∘ Φ` is a function on the total space of a vector bundle whose zero section is critical with
nondegenerate fibre Hessians, the input of the parametric Morse lemma on a vector bundle. The
Morse–Bott lemma on the normal bundle of a Morse–Bott submanifold applies it to `f` read through
a tubular neighbourhood.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm`: if `Φ (0_s) = i s` and the
  derivative of `Φ` at `0_s` is injective, the fibre of `Φ` over `s` is transverse to `i`.
* `IsNondegenerateCriticalSubmanifold.isNondegenerateCriticalPoint_comp_mk_trivializationAt_symm`:
  along a Morse–Bott submanifold, the fibre slices of `f ∘ Φ` have nondegenerate critical points at
  `0`.
* `IsCriticalSubmanifold.morseIndex_comp_mk_trivializationAt_symm`: their Morse index is the Morse
  index of `f` at `i s`.
* `IsNondegenerateCriticalSubmanifold.isNondegenerateCriticalPoint_comp_diffeomorph` and
  `IsCriticalSubmanifold.morseIndex_comp_diffeomorph`: the same for a diffeomorphism of the total
  space onto an open subset of `M`, such as a tubular neighbourhood.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *A proof of the Morse–Bott lemma*, Expositiones Mathematicae 22
  (2004), 365–373.
-/

public noncomputable section

open Bundle Function Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {V : S → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℝ (V s)]
  [∀ s, TopologicalSpace (V s)] [TopologicalSpace (TotalSpace P V)]
  [FiberBundle P V] [VectorBundle ℝ P V]
  {Φ : TotalSpace P V → M} {s : S}

omit [I.Boundaryless] [IsManifold I 2 M] in
/-- **The fibres of a map out of a vector bundle are transverse to the image of its zero
section.** Let `Φ` send the zero section of a vector bundle `V → S` onto the embedded submanifold
`i` near `s`, `Φ (0_s') = i s'`, with injective derivative at `0_s`. If the rank of `V` is the
codimension of `S`, then the fibre of `Φ` over `s`, read in the trivialization at `s`, has
bijective normal derivative at `0`: its derivative at `0` followed by the quotient onto the
normal space of `i` at `s` is bijective. -/
theorem bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (hΦi : ∀ᶠ s' in 𝓝 s, Φ (zeroSection P V s') = i s')
    (hΦ : MDifferentiableAt (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s))
    (hΦ' : Injective (mfderiv (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s))) :
    Bijective fun w : P ↦ i.normalClass s hn (mfderiv 𝓘(ℝ, P) I
      (fun w : P ↦ Φ ⟨s, (trivializationAt P V s).symm s w⟩) 0 w) := by
  set ι : P → TotalSpace P V := fun w ↦ ⟨s, (trivializationAt P V s).symm s w⟩
  have hι0 : ι 0 = zeroSection P V s := TauCeti.Bundle.mk_trivializationAt_symm_zero ℝ s
  have hιd := TauCeti.Bundle.hasMFDerivAt_mk_trivializationAt_symm (I := J) (F := P) (V := V) s 0
  have hζd := TauCeti.Bundle.hasMFDerivAt_zeroSection (I := J) (F := P) (V := V) s
  have hΦι : MDifferentiableAt (J.prod 𝓘(ℝ, P)) I Φ (ι 0) := hι0 ▸ hΦ
  -- Along the fibre, the derivative of `Φ ∘ ι` at `0` is that of `Φ` on vertical vectors.
  have hvert (w : P) : mfderiv 𝓘(ℝ, P) I (Φ ∘ ι) 0 w =
      mfderiv (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s) (0, w) := by
    rw [mfderiv_comp 0 hΦι hιd.mdifferentiableAt, hιd.mfderiv, hι0]
    rfl
  -- Along the zero section, the derivative of `Φ` is that of `i` on horizontal vectors.
  have hhor (ξ : TangentSpace J s) : mfderiv J I i s ξ =
      mfderiv (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s) (ξ, 0) := by
    have hi : Φ ∘ zeroSection P V =ᶠ[𝓝 s] i := hΦi
    have h₁ : mfderiv J I i s ξ = mfderiv J I (Φ ∘ zeroSection P V) s ξ := by
      rw [hi.mfderiv_eq]
      -- `tangentSpaceCast` is by definition the identity of the model space.
      rfl
    have h₂ : mfderiv J I (Φ ∘ zeroSection P V) s ξ =
        mfderiv (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s) (ξ, 0) := by
      rw [mfderiv_comp s hΦ hζd.mdifferentiableAt, hζd.mfderiv]
      rfl
    exact h₁.trans h₂
  -- The normal derivative is a linear map between spaces of the same finite dimension.
  let L : P →ₗ[ℝ] i.NormalSpace s hn :=
    (i.normalClass s hn).comp
      (mfderiv 𝓘(ℝ, P) I (Φ ∘ ι) 0 : P →L[ℝ] TangentSpace I (i s)).toLinearMap
  have hinj : Injective L := by
    refine (injective_iff_map_eq_zero L).mpr fun w hw ↦ ?_
    -- A vertical vector sent into the tangent space of the submanifold is horizontal, so zero.
    obtain ⟨ξ, hξ⟩ : mfderiv 𝓘(ℝ, P) I (Φ ∘ ι) 0 w ∈ i.tangentRange s hn := by
      rw [← normalClass_ker]
      exact hw
    have h' := hΦ' ((hhor ξ).symm.trans (hξ.trans (hvert w)))
    exact (congrArg Prod.snd h').symm
  have hfin : Module.finrank ℝ P = Module.finrank ℝ (i.NormalSpace s hn) := by
    have hsum := i.finrank_normalSpace_add_finrank s hn
    -- The tangent spaces of `S` and `M` are by definition the model spaces `E'` and `E`.
    have hE : Module.finrank ℝ (TangentSpace I (i s)) = Module.finrank ℝ E := rfl
    have hE' : Module.finrank ℝ (TangentSpace J s) = Module.finrank ℝ E' := rfl
    omega
  have : FiniteDimensional ℝ (TangentSpace I (i s)) := inferInstanceAs (FiniteDimensional ℝ E)
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] [FiniteDimensional ℝ P] in
/-- The fibre of `Φ` over `s` passes through `i s`. -/
private theorem comp_mk_trivializationAt_symm_zero
    (hΦi : ∀ᶠ s' in 𝓝 s, Φ (zeroSection P V s') = i s') :
    Φ ⟨s, (trivializationAt P V s).symm s 0⟩ = i s :=
  (congrArg Φ (TauCeti.Bundle.mk_trivializationAt_symm_zero (F := P) (V := V) ℝ s)).trans
    hΦi.self_of_nhds

namespace IsNondegenerateCriticalSubmanifold

include hn in
/-- **Fibre slices along a Morse–Bott submanifold are nondegenerate.** Let `i` be a Morse–Bott
critical submanifold of `f`, and let `Φ` be a map out of a vector bundle `V → S` whose rank is the
codimension of `S`, with `Φ (0_s') = i s'` for `s'` near `s`, `C²` at `0_s` with injective
derivative there. Then the fibre slice `w ↦ f (Φ ⟨s, e.symm s w⟩)` of `f ∘ Φ` over `s`, read in the
trivialization `e` at `s`, has a nondegenerate critical point at `0`. -/
theorem isNondegenerateCriticalPoint_comp_mk_trivializationAt_symm
    (h : i.IsNondegenerateCriticalSubmanifold f)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (hΦi : ∀ᶠ s' in 𝓝 s, Φ (zeroSection P V s') = i s')
    (hΦ : ContMDiffAt (J.prod 𝓘(ℝ, P)) I 2 Φ (zeroSection P V s))
    (hΦ' : Injective (mfderiv (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s))) :
    IsNondegenerateCriticalPoint
      (fun w : P ↦ f (Φ ⟨s, (trivializationAt P V s).symm s w⟩)) 0 :=
  h.isNondegenerateCriticalPoint_comp hn (comp_mk_trivializationAt_symm_zero hΦi)
    (TauCeti.Bundle.contMDiffAt_comp_mk_trivializationAt_symm hΦ)
    (bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm hn hdim hΦi
      (hΦ.mdifferentiableAt two_ne_zero) hΦ')

end IsNondegenerateCriticalSubmanifold

namespace IsCriticalSubmanifold

include hn in
/-- **The index of a fibre slice.** Let `i` be a critical submanifold of `f`, and let `Φ` be a map
out of a vector bundle `V → S` whose rank is the codimension of `S`, with `Φ (0_s') = i s'` for
`s'` near `s`, `C²` at `0_s` with injective derivative there. Then the Morse index at `0` of the
fibre slice `w ↦ f (Φ ⟨s, e.symm s w⟩)` of `f ∘ Φ` over `s`, read in the trivialization `e` at
`s`, is the Morse index of `f` at `i s`. -/
theorem morseIndex_comp_mk_trivializationAt_symm
    (h : i.IsCriticalSubmanifold f)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (hΦi : ∀ᶠ s' in 𝓝 s, Φ (zeroSection P V s') = i s')
    (hΦ : ContMDiffAt (J.prod 𝓘(ℝ, P)) I 2 Φ (zeroSection P V s))
    (hΦ' : Injective (mfderiv (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s))) :
    morseIndex (fun w : P ↦ f (Φ ⟨s, (trivializationAt P V s).symm s w⟩)) 0 =
      manifoldMorseIndex I f (i s) :=
  h.morseIndex_comp hn (comp_mk_trivializationAt_symm_zero hΦi)
    (TauCeti.Bundle.contMDiffAt_comp_mk_trivializationAt_symm hΦ)
    (bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm hn hdim hΦi
      (hΦ.mdifferentiableAt two_ne_zero) hΦ')

end IsCriticalSubmanifold

section Diffeomorph

variable {m : WithTop ℕ∞} {W : TopologicalSpace.Opens M}

omit [I.Boundaryless] [IsManifold I 2 M] [∀ s, Module ℝ (V s)] [VectorBundle ℝ P V] in
/-- If the derivative of `Φ` at `0_s` is invertible, the rank of the bundle is the codimension of
`S`: the tangent space `E' × P` of the total space is isomorphic to the tangent space `E` of `M`. -/
private theorem finrank_eq_sub_of_isInvertible_mfderiv
    (hΦ' : (mfderiv (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s)).IsInvertible) :
    Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E' := by
  obtain ⟨e, -⟩ := hΦ'
  -- The tangent spaces of the total space and of `M` are by definition `E' × P` and `E`.
  let e' : (E' × P) ≃ₗ[ℝ] E := e.toLinearEquiv
  have : FiniteDimensional ℝ (E' × P) := e'.symm.finiteDimensional
  have : FiniteDimensional ℝ E' :=
    Module.Finite.of_injective (LinearMap.inl ℝ E' P) LinearMap.inl_injective
  have h := e'.finrank_eq
  rw [Module.finrank_prod] at h
  omega

namespace IsNondegenerateCriticalSubmanifold

include hn in
/-- **A Morse–Bott function along the fibres of a tubular neighbourhood.** Let `i` be a Morse–Bott
critical submanifold of `f`, and let `Ψ` be a `C^m` diffeomorphism, `2 ≤ m`, from the total space
of a vector bundle `V → S` onto an open subset of `M`, so that the rank of `V` is the codimension
of `S`, with `Ψ (0_s) = i s` for all `s`. Then for every `s` the fibre slice
`w ↦ f (Ψ ⟨s, e.symm s w⟩)` of `f ∘ Ψ` over `s`, read in the trivialization `e` at `s`, has a
nondegenerate critical point at `0`.
The tubular neighbourhood of a smooth embedding
(`TauCeti.SmoothEmbedding.exists_diffeomorph_normalBundle_subset`) is such a diffeomorphism. -/
theorem isNondegenerateCriticalPoint_comp_diffeomorph
    (h : i.IsNondegenerateCriticalSubmanifold f) (hm : 2 ≤ m)
    (Ψ : TotalSpace P V ≃ₘ^m⟮J.prod 𝓘(ℝ, P), I⟯ W) (hΨi : ∀ s, (Ψ (zeroSection P V s) : M) = i s)
    (s : S) :
    IsNondegenerateCriticalPoint
      (fun w : P ↦ f (Ψ ⟨s, (trivializationAt P V s).symm s w⟩)) 0 := by
  -- The diffeomorphism followed by the inclusion of `W` is a local diffeomorphism.
  have hloc : IsLocalDiffeomorphAt (J.prod 𝓘(ℝ, P)) I m (Subtype.val ∘ Ψ) (zeroSection P V s) :=
    IsLocalDiffeomorphAt.comp (K := I) (P := M) (Ψ.isLocalDiffeomorph _)
      (isLocalDiffeomorph_subtype_val _)
  have hΨ' := hloc.isInvertible_mfderiv (lt_of_lt_of_le (by norm_num) hm).ne'
  exact h.isNondegenerateCriticalPoint_comp_mk_trivializationAt_symm hn
    (finrank_eq_sub_of_isInvertible_mfderiv hΨ') (Filter.Eventually.of_forall hΨi)
    (hloc.contMDiffAt.of_le hm) hΨ'.injective

end IsNondegenerateCriticalSubmanifold

namespace IsCriticalSubmanifold

include hn in
/-- **The index of a fibre slice of a tubular neighbourhood.** Let `i` be a critical submanifold of
`f`, and let `Ψ` be a `C^m` diffeomorphism, `2 ≤ m`, from the total space of a vector bundle
`V → S` onto an open subset of `M`, so that the rank of `V` is the codimension of `S`, with
`Ψ (0_s) = i s` for all `s`. Then for every `s` the Morse index at `0` of the fibre slice
`w ↦ f (Ψ ⟨s, e.symm s w⟩)`, read in the trivialization `e` at `s`, is the Morse index of `f` at
`i s`. -/
theorem morseIndex_comp_diffeomorph (h : i.IsCriticalSubmanifold f) (hm : 2 ≤ m)
    (Ψ : TotalSpace P V ≃ₘ^m⟮J.prod 𝓘(ℝ, P), I⟯ W) (hΨi : ∀ s, (Ψ (zeroSection P V s) : M) = i s)
    (s : S) :
    morseIndex (fun w : P ↦ f (Ψ ⟨s, (trivializationAt P V s).symm s w⟩)) 0 =
      manifoldMorseIndex I f (i s) := by
  -- The diffeomorphism followed by the inclusion of `W` is a local diffeomorphism.
  have hloc : IsLocalDiffeomorphAt (J.prod 𝓘(ℝ, P)) I m (Subtype.val ∘ Ψ) (zeroSection P V s) :=
    IsLocalDiffeomorphAt.comp (K := I) (P := M) (Ψ.isLocalDiffeomorph _)
      (isLocalDiffeomorph_subtype_val _)
  have hΨ' := hloc.isInvertible_mfderiv (lt_of_lt_of_le (by norm_num) hm).ne'
  exact h.morseIndex_comp_mk_trivializationAt_symm hn
    (finrank_eq_sub_of_isInvertible_mfderiv hΨ') (Filter.Eventually.of_forall hΨi)
    (hloc.contMDiffAt.of_le hm) hΨ'.injective

end IsCriticalSubmanifold

end Diffeomorph

end TauCeti.SmoothEmbedding
