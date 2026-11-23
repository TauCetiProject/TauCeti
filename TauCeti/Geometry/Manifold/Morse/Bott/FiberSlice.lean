/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Morse.Bott.Slice
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.ZeroSection
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# A Morse–Bott function along the fibres of a tubular neighbourhood

Let `i : S → M` be a critical submanifold of a function `f` on a boundaryless manifold, and let
`V → S` be a vector bundle with model fibre `P` whose rank is the codimension of `S`. Let
`Φ : V → M` be a map out of the total space which sends the zero section onto the submanifold,
`Φ (0_s) = i s`, and has injective derivative at `0_s`, as the tubular neighbourhood of `S` given
by the normal bundle (`TauCeti.SmoothEmbedding.exists_diffeomorph_normalBundle_subset`) does. This
file reads `f` along the fibres of `Φ`: over `s`, the **fibre slice**

`w ↦ f (Φ ⟨s, e.symm s w⟩)`, with `e = trivializationAt P V s`,

is a function on the model fibre `P`, the fibre of `f ∘ Φ` over `s` read in the preferred
trivialization at `s`.

Each fibre of `Φ` is a transverse slice through the submanifold
(`TauCeti.SmoothEmbedding.bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm`), so the
results of `TauCeti.Geometry.Manifold.Morse.Bott.Slice` apply: the fibre slice has a critical
point at `0`, whose Hessian is the normal Hessian evaluated on the normal classes of the images of
vertical vectors under the derivative of `Φ`. Its Morse index there is the Morse index of `f` at
`i s`, and when `i` is Morse–Bott, this critical point is nondegenerate.

When the fibres of `V` are normed spaces, the fibre slice is the intrinsic fibre restriction
`v ↦ f (Φ ⟨s, v⟩)` read through the trivialization at `s`, which is a linear isomorphism on the
fibre. The two have the same nondegenerate critical points and Morse indices at `0`. So for a
tubular neighbourhood `Ψ`, the function `f ∘ Ψ` on the total space has, along the zero section,
critical fibre restrictions with invertible Hessians: the input of the parametric Morse lemma on a
vector bundle (`TauCeti.exists_parametric_morse_partialDiffeomorph`).

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsCriticalSubmanifold.fderiv_comp_mk_trivializationAt_symm_eq_zero` and
  `IsCriticalSubmanifold.fderiv_fderiv_comp_mk_trivializationAt_symm_apply`: the fibre slices of
  `f ∘ Φ` are critical at `0`, with Hessian the normal Hessian on vertical vectors.
* `IsNondegenerateCriticalSubmanifold.isNondegenerateCriticalPoint_comp_mk_trivializationAt_symm`:
  along a Morse–Bott submanifold, the fibre slices of `f ∘ Φ` have nondegenerate critical points at
  `0`.
* `IsCriticalSubmanifold.morseIndex_comp_mk_trivializationAt_symm`: their Morse index is the Morse
  index of `f` at `i s`.
* The `_of_isLocalDiffeomorphAt` variants of the last two, for `Φ` a local diffeomorphism at `0_s`,
  and the `_comp_diffeomorph_mk_trivializationAt_symm` variants, for a diffeomorphism of the total
  space onto an open subset of `M`, such as a tubular neighbourhood. For these the rank of `V` is
  automatically the codimension of `S`.
* `IsNondegenerateCriticalSubmanifold.isNondegenerateCriticalPoint_comp_diffeomorph_mk` and
  `IsCriticalSubmanifold.morseIndex_comp_diffeomorph_mk`: the same for the intrinsic fibre
  restrictions of `f` read through a tubular neighbourhood, when the fibres are normed.
* `IsCriticalSubmanifold.fderiv_fderiv_comp_mk_apply`: the Hessian of the intrinsic fibre
  restriction `v ↦ f (Φ ⟨s, v⟩)` is the normal Hessian on vertical vectors, when the fibres are
  normed.

In the namespace `TauCeti.Bundle`, `isNondegenerateCriticalPoint_comp_mk_iff`,
`morseIndex_comp_mk` and `fderiv_fderiv_comp_mk_apply` compare the intrinsic fibre restriction
`v ↦ g ⟨s, v⟩` of any function `g` on the total space with its reading in the trivialization at
`s`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *A proof of the Morse–Bott lemma*, Expositiones Mathematicae 22
  (2004), 365–373.
-/

public noncomputable section

open Bundle Function Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {S P : Type*} [TopologicalSpace S] [NormedAddCommGroup P] [NormedSpace ℝ P]
  {V : S → Type*} [TopologicalSpace (TotalSpace P V)]

section NormedFibre

variable [∀ s, NormedAddCommGroup (V s)] [∀ s, NormedSpace ℝ (V s)]
  [FiberBundle P V] [VectorBundle ℝ P V]

namespace Bundle

/-- A function on the total space of a vector bundle with normed fibres has a nondegenerate
critical point at `0` along the fibre over `s` exactly when it has one along the fibre read in the
trivialization at `s`. -/
theorem isNondegenerateCriticalPoint_comp_mk_iff (g : TotalSpace P V → ℝ) (s : S) :
    IsNondegenerateCriticalPoint (fun v : V s ↦ g ⟨s, v⟩) 0 ↔
      IsNondegenerateCriticalPoint (fun w : P ↦ g ⟨s, (trivializationAt P V s).symm s w⟩) 0 := by
  set e := (trivializationAt P V s).continuousLinearEquivAt ℝ s
    (mem_baseSet_trivializationAt P V s)
  have hcomp := (trivializationAt P V s).comp_mk_eq_comp_continuousLinearEquivAt ℝ g
    (mem_baseSet_trivializationAt P V s)
  -- The reading in the trivialization is the intrinsic fibre restriction composed with `e⁻¹`.
  have hcomp' : (fun w : P ↦ g ⟨s, (trivializationAt P V s).symm s w⟩) =
      (fun v : V s ↦ g ⟨s, v⟩) ∘ e.symm := by
    rw [hcomp, Function.comp_assoc, ContinuousLinearEquiv.self_comp_symm, Function.comp_id]
  constructor
  · intro h
    rw [hcomp']
    refine IsNondegenerateCriticalPoint.comp ?_ e.symm.contDiff.contDiffAt ?_
    · rwa [map_zero]
    · rw [e.symm.fderiv]
      exact ⟨e.symm, rfl⟩
  · intro h
    rw [hcomp]
    refine IsNondegenerateCriticalPoint.comp ?_ e.contDiff.contDiffAt ?_
    · rwa [map_zero]
    · rw [e.fderiv]
      exact ⟨e, rfl⟩

/-- If a function on the total space of a vector bundle with normed fibres is `C²` and critical at
`0` along the fibre over `s` read in the trivialization at `s`, its Morse index there is that of
the intrinsic fibre restriction. -/
theorem morseIndex_comp_mk {g : TotalSpace P V → ℝ} {s : S}
    (hg : ContDiffAt ℝ 2 (fun w : P ↦ g ⟨s, (trivializationAt P V s).symm s w⟩) 0)
    (hcrit : fderiv ℝ (fun w : P ↦ g ⟨s, (trivializationAt P V s).symm s w⟩) 0 = 0) :
    morseIndex (fun v : V s ↦ g ⟨s, v⟩) 0 =
      morseIndex (fun w : P ↦ g ⟨s, (trivializationAt P V s).symm s w⟩) 0 := by
  set e := (trivializationAt P V s).continuousLinearEquivAt ℝ s
    (mem_baseSet_trivializationAt P V s)
  rw [(trivializationAt P V s).comp_mk_eq_comp_continuousLinearEquivAt ℝ g
      (mem_baseSet_trivializationAt P V s),
    morseIndex_comp ((map_zero e).symm ▸ hg) e.contDiff.contDiffAt ((map_zero e).symm ▸ hcrit)
      (e.fderiv ▸ ⟨e, rfl⟩), map_zero]

/-- The second derivative at `0` of the intrinsic fibre restriction over `s` of a function on the
total space of a vector bundle with normed fibres is that of its reading in the trivialization at
`s`, evaluated on the images of the vectors under that trivialization. No differentiability is
needed. -/
theorem fderiv_fderiv_comp_mk_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : TotalSpace P V → G) (s : S) (u v : V s) :
    fderiv ℝ (fderiv ℝ (fun v : V s ↦ g ⟨s, v⟩)) 0 u v =
      fderiv ℝ (fderiv ℝ (fun w : P ↦ g ⟨s, (trivializationAt P V s).symm s w⟩)) 0
        ((trivializationAt P V s).continuousLinearEquivAt ℝ s
          (mem_baseSet_trivializationAt P V s) u)
        ((trivializationAt P V s).continuousLinearEquivAt ℝ s
          (mem_baseSet_trivializationAt P V s) v) := by
  rw [(trivializationAt P V s).comp_mk_eq_comp_continuousLinearEquivAt ℝ g
      (mem_baseSet_trivializationAt P V s),
    ContinuousLinearEquiv.fderiv_fderiv_comp_right_apply_apply, map_zero]

end Bundle

end NormedFibre

namespace SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  {Φ : TotalSpace P V → M} {s : S} {m : WithTop ℕ∞} {W : TopologicalSpace.Opens M}

section Trivialized

variable [∀ s, AddCommMonoid (V s)] [∀ s, Module ℝ (V s)] [∀ s, TopologicalSpace (V s)]
  [FiberBundle P V] [VectorBundle ℝ P V]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
/-- The fibre of `Φ` over `s` passes through `i s`. -/
private theorem comp_mk_trivializationAt_symm_zero
    (hΦi : ∀ᶠ s' in 𝓝 s, Φ (zeroSection P V s') = i s') :
    Φ ⟨s, (trivializationAt P V s).symm s 0⟩ = i s :=
  (congrArg Φ (mk_trivializationAt_symm_zero (F := P) (E := V) ℝ s)).trans hΦi.self_of_nhds

namespace IsCriticalSubmanifold

variable (h : i.IsCriticalSubmanifold f)
include h

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
/-- **Fibre slices through a critical submanifold are critical.** Let `i` be a critical
submanifold of `f`, and let `Φ` be a map out of a vector bundle `V → S`, with `Φ (0_s') = i s'`
for `s'` near `s`, differentiable at `0_s`. Then the fibre slice `w ↦ f (Φ ⟨s, e.symm s w⟩)` of
`f ∘ Φ` over `s`, read in the trivialization `e` at `s`, is critical at `0`. -/
theorem fderiv_comp_mk_trivializationAt_symm_eq_zero
    (hΦi : ∀ᶠ s' in 𝓝 s, Φ (zeroSection P V s') = i s')
    (hΦ : MDifferentiableAt (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s)) :
    fderiv ℝ (fun w : P ↦ f (Φ ⟨s, (trivializationAt P V s).symm s w⟩)) 0 = 0 :=
  h.fderiv_comp_eq_zero (comp_mk_trivializationAt_symm_zero hΦi)
    (((mk_trivializationAt_symm_zero (F := P) (E := V) ℝ s).symm ▸ hΦ).comp 0
      (TauCeti.Bundle.hasMFDerivAt_mk_trivializationAt_symm (I := J) s 0).mdifferentiableAt)

omit [FiniteDimensional ℝ E] in
/-- **The Hessian of a fibre slice is the normal Hessian.** Let `i` be a critical submanifold of
`f`, and let `Φ` be a map out of a vector bundle `V → S`, with `Φ (0_s') = i s'` for `s'` near `s`,
`C²` at `0_s`. Then the Hessian at `0` of the fibre slice `w ↦ f (Φ ⟨s, e.symm s w⟩)` of `f ∘ Φ`
over `s`, read in the trivialization `e` at `s`, is the normal Hessian at `s` evaluated on the
normal classes of the images of the vertical vectors `(0, u)` and `(0, w)` under the derivative of
`Φ` at `0_s`. -/
theorem fderiv_fderiv_comp_mk_trivializationAt_symm_apply
    (hΦi : ∀ᶠ s' in 𝓝 s, Φ (zeroSection P V s') = i s')
    (hΦ : ContMDiffAt (J.prod 𝓘(ℝ, P)) I 2 Φ (zeroSection P V s)) (u w : P) :
    fderiv ℝ (fderiv ℝ (fun w : P ↦ f (Φ ⟨s, (trivializationAt P V s).symm s w⟩))) 0 u w =
      h.normalHessian hn s
        (i.normalClass s hn (mfderiv (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s) (0, u)))
        (i.normalClass s hn (mfderiv (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s) (0, w))) := by
  have hΦd := hΦ.mdifferentiableAt two_ne_zero
  rw [← TauCeti.Bundle.mfderiv_comp_mk_trivializationAt_symm_zero_apply hΦd,
    ← TauCeti.Bundle.mfderiv_comp_mk_trivializationAt_symm_zero_apply hΦd]
  exact h.fderiv_fderiv_comp_apply hn (φ := fun w : P ↦ Φ ⟨s, (trivializationAt P V s).symm s w⟩)
    (y := 0) (comp_mk_trivializationAt_symm_zero hΦi) hΦ.comp_mk_trivializationAt_symm u w

include hn in
/-- **The index of a fibre slice.** Let `i` be a critical submanifold of `f`, and let `Φ` be a map
out of a vector bundle `V → S` whose rank is the codimension of `S`, with `Φ (0_s') = i s'` for
`s'` near `s`, `C²` at `0_s` with injective derivative there. Then the Morse index at `0` of the
fibre slice `w ↦ f (Φ ⟨s, e.symm s w⟩)` of `f ∘ Φ` over `s`, read in the trivialization `e` at
`s`, is the Morse index of `f` at `i s`. -/
theorem morseIndex_comp_mk_trivializationAt_symm
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (hΦi : ∀ᶠ s' in 𝓝 s, Φ (zeroSection P V s') = i s')
    (hΦ : ContMDiffAt (J.prod 𝓘(ℝ, P)) I 2 Φ (zeroSection P V s))
    (hΦ' : Injective (mfderiv (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s))) :
    morseIndex (fun w : P ↦ f (Φ ⟨s, (trivializationAt P V s).symm s w⟩)) 0 =
      manifoldMorseIndex I f (i s) :=
  h.morseIndex_comp hn (comp_mk_trivializationAt_symm_zero hΦi)
    hΦ.comp_mk_trivializationAt_symm
    (bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm hn hdim hΦi hΦ')

include hn in
/-- **The index of a fibre slice of a local diffeomorphism.** Let `i` be a critical submanifold of
`f`, and let `Φ` be a map out of a vector bundle `V → S` which is a `C^m` local diffeomorphism at
`0_s`, `2 ≤ m`, with `Φ (0_s') = i s'` for `s'` near `s`. Then the Morse index at `0` of the fibre
slice `w ↦ f (Φ ⟨s, e.symm s w⟩)` of `f ∘ Φ` over `s`, read in the trivialization `e` at `s`, is
the Morse index of `f` at `i s`. -/
theorem morseIndex_comp_mk_trivializationAt_symm_of_isLocalDiffeomorphAt (hm : 2 ≤ m)
    (hΦi : ∀ᶠ s' in 𝓝 s, Φ (zeroSection P V s') = i s')
    (hΦ : IsLocalDiffeomorphAt (J.prod 𝓘(ℝ, P)) I m Φ (zeroSection P V s)) :
    morseIndex (fun w : P ↦ f (Φ ⟨s, (trivializationAt P V s).symm s w⟩)) 0 =
      manifoldMorseIndex I f (i s) :=
  h.morseIndex_comp hn (comp_mk_trivializationAt_symm_zero hΦi)
    (hΦ.contMDiffAt.of_le hm).comp_mk_trivializationAt_symm
    (bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm_of_isInvertible hn hΦi
      (hΦ.isInvertible_mfderiv (lt_of_lt_of_le (by norm_num) hm).ne'))

include hn in
/-- **The index of a fibre slice of a tubular neighbourhood.** Let `i` be a critical submanifold of
`f`, and let `Ψ` be a `C^m` diffeomorphism, `2 ≤ m`, from the total space of a vector bundle
`V → S` onto an open subset of `M`, with `Ψ (0_s) = i s` for all `s`. Then for every `s` the Morse
index at `0` of the fibre slice `w ↦ f (Ψ ⟨s, e.symm s w⟩)`, read in the trivialization `e` at
`s`, is the Morse index of `f` at `i s`. -/
theorem morseIndex_comp_diffeomorph_mk_trivializationAt_symm (hm : 2 ≤ m)
    (Ψ : TotalSpace P V ≃ₘ^m⟮J.prod 𝓘(ℝ, P), I⟯ W) (hΨi : ∀ s, (Ψ (zeroSection P V s) : M) = i s)
    (s : S) :
    morseIndex (fun w : P ↦ f (Ψ ⟨s, (trivializationAt P V s).symm s w⟩)) 0 =
      manifoldMorseIndex I f (i s) :=
  h.morseIndex_comp_mk_trivializationAt_symm_of_isLocalDiffeomorphAt hn hm
    (Filter.Eventually.of_forall hΨi)
    (Ψ.isLocalDiffeomorph_subtypeVal_comp _)

end IsCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable (h : i.IsNondegenerateCriticalSubmanifold f)
include h

include hn in
/-- **Fibre slices along a Morse–Bott submanifold are nondegenerate.** Let `i` be a Morse–Bott
critical submanifold of `f`, and let `Φ` be a map out of a vector bundle `V → S` whose rank is the
codimension of `S`, with `Φ (0_s') = i s'` for `s'` near `s`, `C²` at `0_s` with injective
derivative there. Then the fibre slice `w ↦ f (Φ ⟨s, e.symm s w⟩)` of `f ∘ Φ` over `s`, read in the
trivialization `e` at `s`, has a nondegenerate critical point at `0`. -/
theorem isNondegenerateCriticalPoint_comp_mk_trivializationAt_symm
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (hΦi : ∀ᶠ s' in 𝓝 s, Φ (zeroSection P V s') = i s')
    (hΦ : ContMDiffAt (J.prod 𝓘(ℝ, P)) I 2 Φ (zeroSection P V s))
    (hΦ' : Injective (mfderiv (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s))) :
    IsNondegenerateCriticalPoint
      (fun w : P ↦ f (Φ ⟨s, (trivializationAt P V s).symm s w⟩)) 0 :=
  have : FiniteDimensional ℝ (E' × P) := TauCeti.finiteDimensional_of_injective_mfderiv hΦ'
  have : FiniteDimensional ℝ P :=
    Module.Finite.of_injective (LinearMap.inr ℝ E' P) LinearMap.inr_injective
  h.isNondegenerateCriticalPoint_comp hn (comp_mk_trivializationAt_symm_zero hΦi)
    hΦ.comp_mk_trivializationAt_symm
    (bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm hn hdim hΦi hΦ')

include hn in
/-- **Fibre slices of a local diffeomorphism along a Morse–Bott submanifold are nondegenerate.**
Let `i` be a Morse–Bott critical submanifold of `f`, and let `Φ` be a map out of a vector bundle
`V → S` which is a `C^m` local diffeomorphism at `0_s`, `2 ≤ m`, with `Φ (0_s') = i s'` for `s'`
near `s`. Then the fibre slice `w ↦ f (Φ ⟨s, e.symm s w⟩)` of `f ∘ Φ` over `s`, read in the
trivialization `e` at `s`, has a nondegenerate critical point at `0`. -/
theorem isNondegenerateCriticalPoint_comp_mk_trivializationAt_symm_of_isLocalDiffeomorphAt
    (hm : 2 ≤ m) (hΦi : ∀ᶠ s' in 𝓝 s, Φ (zeroSection P V s') = i s')
    (hΦ : IsLocalDiffeomorphAt (J.prod 𝓘(ℝ, P)) I m Φ (zeroSection P V s)) :
    IsNondegenerateCriticalPoint
      (fun w : P ↦ f (Φ ⟨s, (trivializationAt P V s).symm s w⟩)) 0 :=
  have hΦ' := hΦ.isInvertible_mfderiv (lt_of_lt_of_le (by norm_num) hm).ne'
  have : FiniteDimensional ℝ (E' × P) :=
    TauCeti.finiteDimensional_of_injective_mfderiv hΦ'.injective
  have : FiniteDimensional ℝ P :=
    Module.Finite.of_injective (LinearMap.inr ℝ E' P) LinearMap.inr_injective
  h.isNondegenerateCriticalPoint_comp hn (comp_mk_trivializationAt_symm_zero hΦi)
    (hΦ.contMDiffAt.of_le hm).comp_mk_trivializationAt_symm
    (bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm_of_isInvertible hn hΦi hΦ')

include hn in
/-- **A Morse–Bott function along the fibres of a tubular neighbourhood.** Let `i` be a Morse–Bott
critical submanifold of `f`, and let `Ψ` be a `C^m` diffeomorphism, `2 ≤ m`, from the total space
of a vector bundle `V → S` onto an open subset of `M`, with `Ψ (0_s) = i s` for all `s`. Then for
every `s` the fibre slice `w ↦ f (Ψ ⟨s, e.symm s w⟩)` of `f ∘ Ψ` over `s`, read in the
trivialization `e` at `s`, has a nondegenerate critical point at `0`.
The tubular neighbourhood of a smooth embedding
(`TauCeti.SmoothEmbedding.exists_diffeomorph_normalBundle_subset`) is such a diffeomorphism. -/
theorem isNondegenerateCriticalPoint_comp_diffeomorph_mk_trivializationAt_symm (hm : 2 ≤ m)
    (Ψ : TotalSpace P V ≃ₘ^m⟮J.prod 𝓘(ℝ, P), I⟯ W) (hΨi : ∀ s, (Ψ (zeroSection P V s) : M) = i s)
    (s : S) :
    IsNondegenerateCriticalPoint
      (fun w : P ↦ f (Ψ ⟨s, (trivializationAt P V s).symm s w⟩)) 0 :=
  h.isNondegenerateCriticalPoint_comp_mk_trivializationAt_symm_of_isLocalDiffeomorphAt hn hm
    (Filter.Eventually.of_forall hΨi)
    (Ψ.isLocalDiffeomorph_subtypeVal_comp _)

end IsNondegenerateCriticalSubmanifold

end Trivialized

section NormedFibre

variable [∀ s, NormedAddCommGroup (V s)] [∀ s, NormedSpace ℝ (V s)]
  [FiberBundle P V] [VectorBundle ℝ P V]

omit [FiniteDimensional ℝ E] in
/-- **The Hessian of an intrinsic fibre restriction is the normal Hessian.** Let `i` be a critical
submanifold of `f`, and let `Φ` be a map out of a vector bundle `V → S` with normed fibres, with
`Φ (0_s') = i s'` for `s'` near `s`, `C²` at `0_s`. Then the Hessian at `0` of the fibre
restriction `v ↦ f (Φ ⟨s, v⟩)` of `f ∘ Φ` over `s` is the normal Hessian at `s` evaluated on the
normal classes of the images under the derivative of `Φ` at `0_s` of the vertical vectors given by
`u` and `v`, read in the trivialization `e` at `s`. -/
theorem IsCriticalSubmanifold.fderiv_fderiv_comp_mk_apply (h : i.IsCriticalSubmanifold f)
    (hΦi : ∀ᶠ s' in 𝓝 s, Φ (zeroSection P V s') = i s')
    (hΦ : ContMDiffAt (J.prod 𝓘(ℝ, P)) I 2 Φ (zeroSection P V s)) (u v : V s) :
    fderiv ℝ (fderiv ℝ (fun v : V s ↦ f (Φ ⟨s, v⟩))) 0 u v =
      h.normalHessian hn s
        (i.normalClass s hn (mfderiv (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s)
          (0, (trivializationAt P V s).continuousLinearEquivAt ℝ s
            (mem_baseSet_trivializationAt P V s) u)))
        (i.normalClass s hn (mfderiv (J.prod 𝓘(ℝ, P)) I Φ (zeroSection P V s)
          (0, (trivializationAt P V s).continuousLinearEquivAt ℝ s
            (mem_baseSet_trivializationAt P V s) v))) := by
  rw [TauCeti.Bundle.fderiv_fderiv_comp_mk_apply (fun x ↦ f (Φ x)) s u v]
  exact h.fderiv_fderiv_comp_mk_trivializationAt_symm_apply hn hΦi hΦ _ _

include hn in
/-- **A Morse–Bott function along the fibres of a tubular neighbourhood, intrinsically.** Let `i`
be a Morse–Bott critical submanifold of `f`, and let `Ψ` be a `C^m` diffeomorphism, `2 ≤ m`, from
the total space of a vector bundle `V → S` with normed fibres onto an open subset of `M`, with
`Ψ (0_s) = i s` for all `s`. Then for every `s` the fibre restriction `v ↦ f (Ψ ⟨s, v⟩)` of
`f ∘ Ψ` over `s` has a nondegenerate critical point at `0`. -/
theorem IsNondegenerateCriticalSubmanifold.isNondegenerateCriticalPoint_comp_diffeomorph_mk
    (h : i.IsNondegenerateCriticalSubmanifold f) (hm : 2 ≤ m)
    (Ψ : TotalSpace P V ≃ₘ^m⟮J.prod 𝓘(ℝ, P), I⟯ W) (hΨi : ∀ s, (Ψ (zeroSection P V s) : M) = i s)
    (s : S) :
    IsNondegenerateCriticalPoint (fun v : V s ↦ f (Ψ ⟨s, v⟩)) 0 :=
  (TauCeti.Bundle.isNondegenerateCriticalPoint_comp_mk_iff (fun x ↦ f (Ψ x)) s).2
    (h.isNondegenerateCriticalPoint_comp_diffeomorph_mk_trivializationAt_symm hn hm Ψ hΨi s)

include hn in
/-- **The index of a fibre restriction of a tubular neighbourhood.** Let `i` be a critical
submanifold of `f`, and let `Ψ` be a `C^m` diffeomorphism, `2 ≤ m`, from the total space of a
vector bundle `V → S` with normed fibres onto an open subset of `M`, with `Ψ (0_s) = i s` for all
`s`. Then for every `s` the Morse index at `0` of the fibre restriction `v ↦ f (Ψ ⟨s, v⟩)` is the
Morse index of `f` at `i s`. -/
theorem IsCriticalSubmanifold.morseIndex_comp_diffeomorph_mk (h : i.IsCriticalSubmanifold f)
    (hm : 2 ≤ m) (Ψ : TotalSpace P V ≃ₘ^m⟮J.prod 𝓘(ℝ, P), I⟯ W)
    (hΨi : ∀ s, (Ψ (zeroSection P V s) : M) = i s) (s : S) :
    morseIndex (fun v : V s ↦ f (Ψ ⟨s, v⟩)) 0 = manifoldMorseIndex I f (i s) := by
  have hΨ := Ψ.isLocalDiffeomorph_subtypeVal_comp (zeroSection P V s)
  have hΨi' : ∀ᶠ s' in 𝓝 s, (Ψ (zeroSection P V s') : M) = i s' := Filter.Eventually.of_forall hΨi
  have hΨ2 := hΨ.contMDiffAt.of_le hm
  -- The fibre slice read in the trivialization at `s` is `C²` and critical at `0`.
  have hf : ContMDiffAt I 𝓘(ℝ) 2 f (Ψ ⟨s, (trivializationAt P V s).symm s 0⟩) :=
    (comp_mk_trivializationAt_symm_zero (Φ := fun x ↦ (Ψ x : M)) hΨi').symm ▸ h.contMDiffAt s
  exact (TauCeti.Bundle.morseIndex_comp_mk (g := fun x ↦ f (Ψ x))
    (hf.comp 0 hΨ2.comp_mk_trivializationAt_symm).contDiffAt
    (h.fderiv_comp_mk_trivializationAt_symm_eq_zero hΨi' (hΨ2.mdifferentiableAt two_ne_zero))).trans
    (h.morseIndex_comp_diffeomorph_mk_trivializationAt_symm hn hm Ψ hΨi s)

end NormedFibre

end SmoothEmbedding

end TauCeti
