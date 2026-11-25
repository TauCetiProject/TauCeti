/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
import TauCeti.LinearAlgebra.TensorProduct.Kernel
import TauCeti.RingTheory.Flat.Extensions

/-!
# Homology of a complex of modules after extension of scalars

The homology of a complex `M₁ --f--> M₂ --g--> M₃` of `R`-modules at `M₂` is written
`(ker g).map (range f).mkQ`: the image of the cycles `ker g` in the cokernel `M₂ ⧸ range f`.
For an `R`-algebra `S` there is a canonical `S`-linear base change map

`S ⊗[R] H(M₁ → M₂ → M₃) → H(S ⊗[R] M₁ → S ⊗[R] M₂ → S ⊗[R] M₃)`,

sending `s ⊗ [m]` to `[s ⊗ m]` (`LinearMap.homologyBaseChange`). It is defined through the
identification `LinearMap.cokernelBaseChangeEquiv` of `S ⊗[R] (M₂ ⧸ range f)` with the cokernel
of `f.baseChange S`. In general it is neither injective nor surjective. This file proves that it
is surjective when the cokernel `M₃ ⧸ range g` is flat, injective when the image `range g` is
flat, and hence bijective for every `S` when `M₃` and `M₃ ⧸ range g` are both flat.

When the homology of `M₁ → M₂ → M₃` computes the cohomology `Hⁱ(X, F)` of a family `X → Spec R`
and its base changes, these maps are the base change maps `R' ⊗ Hⁱ(X, F) → Hⁱ(X_{R'}, F_{R'})` of
cohomology and base change.

## Main declarations

* `LinearMap.homologyBaseChange`: the base change map on homology.
* `LinearMap.homologyBaseChange_surjective`: it is surjective when `M₃ ⧸ range g` is flat.
* `LinearMap.homologyBaseChange_injective`: it is injective when `range g` is flat.
* `LinearMap.homologyBaseChange_bijective`: it is bijective when `M₃` and `M₃ ⧸ range g` are flat.
* `LinearMap.quotientRangeToRange`, `LinearMap.exact_subtype_quotientRangeToRange`: the short
  exact sequence `0 → H → M₂ ⧸ range f → range g → 0` presenting homology.
* `LinearMap.flat_homology`, `LinearMap.finite_homology`, `LinearMap.finitePresentation_homology`:
  flatness and finiteness of homology, from the short exact sequence
  `0 → H → M₂ ⧸ range f → range g → 0`.

## References

* D. Mumford, *Abelian Varieties*, §5.
* R. Hartshorne, *Algebraic Geometry*, §III.12.
-/

public section

open TensorProduct

namespace LinearMap

variable {R : Type*} (S : Type*) {M₁ M₂ M₃ : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
  (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)

/-- The base change map on homology: for a complex `M₁ --f--> M₂ --g--> M₃` and an `R`-algebra
`S`, the `S`-linear map `S ⊗[R] H(M₁ → M₂ → M₃) → H(S ⊗[R] M₁ → S ⊗[R] M₂ → S ⊗[R] M₃)` sending
`s ⊗ [m]` to `[s ⊗ m]`. Homology is the image of the cycles in the cokernel of the incoming map. -/
noncomputable def homologyBaseChange :
    S ⊗[R] (ker g).map (range f).mkQ →ₗ[S]
      (ker (g.baseChange S)).map (range (f.baseChange S)).mkQ :=
  codRestrict _ (f.cokernelBaseChangeEquiv.toLinearMap ∘ₗ
      ((ker g).map (range f).mkQ).subtype.baseChange S) fun x ↦ by
    induction x with
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul s x =>
      obtain ⟨_, ⟨m, hm, rfl⟩⟩ := x
      exact ⟨s ⊗ₜ m, by simp_all, by simp⟩

/-- The base change map on homology sends `s ⊗ x` to the image of `s ⊗ x` under the
identification of `S ⊗[R] (M₂ ⧸ range f)` with the cokernel of `f.baseChange S`. -/
@[simp]
theorem coe_homologyBaseChange_tmul (s : S) (x : (ker g).map (range f).mkQ) :
    (homologyBaseChange S f g (s ⊗ₜ x) : (S ⊗[R] M₂) ⧸ range (f.baseChange S)) =
      f.cokernelBaseChangeEquiv (s ⊗ₜ (x : M₂ ⧸ range f)) :=
  (rfl)

/-- The base change map on homology, followed by the inclusion into the cokernel of
`f.baseChange S`, is the base change of the inclusion of homology into `M₂ ⧸ range f`, followed
by `cokernelBaseChangeEquiv`. -/
theorem subtype_comp_homologyBaseChange :
    ((ker (g.baseChange S)).map (range (f.baseChange S)).mkQ).subtype ∘ₗ
        homologyBaseChange S f g =
      f.cokernelBaseChangeEquiv.toLinearMap ∘ₗ
        ((ker g).map (range f).mkQ).subtype.baseChange S :=
  (rfl)

variable {f g}

/-- The surjection `M₂ ⧸ range f → range g` induced by `g`. Its kernel is the homology
(`LinearMap.ker_quotientRangeToRange`), so homology sits in a short exact sequence
`0 → H → M₂ ⧸ range f → range g → 0` (`LinearMap.exact_subtype_quotientRangeToRange`). -/
noncomputable def quotientRangeToRange (hfg : g ∘ₗ f = 0) : M₂ ⧸ range f →ₗ[R] range g :=
  (range f).liftQ g.rangeRestrict (by rw [ker_rangeRestrict]; exact range_le_ker_iff.2 hfg)

/-- The map `M₂ ⧸ range f → range g` induced by `g` sends the class of `m` to `g m`. -/
@[simp]
theorem coe_quotientRangeToRange_mk (hfg : g ∘ₗ f = 0) (m : M₂) :
    (quotientRangeToRange hfg (Submodule.Quotient.mk m) : M₃) = g m :=
  (rfl)

/-- The map `M₂ ⧸ range f → range g` induced by `g` is surjective. -/
theorem quotientRangeToRange_surjective (hfg : g ∘ₗ f = 0) :
    Function.Surjective (quotientRangeToRange hfg) := by
  rintro ⟨_, ⟨m, rfl⟩⟩
  exact ⟨Submodule.Quotient.mk m, Subtype.ext (coe_quotientRangeToRange_mk hfg m)⟩

/-- The kernel of the map `M₂ ⧸ range f → range g` induced by `g` is the homology
`(ker g).map (range f).mkQ`. -/
theorem ker_quotientRangeToRange (hfg : g ∘ₗ f = 0) :
    ker (quotientRangeToRange hfg) = (ker g).map (range f).mkQ := by
  rw [quotientRangeToRange, Submodule.ker_liftQ, ker_rangeRestrict]

/-- Homology sits in a short exact sequence `0 → H → M₂ ⧸ range f → range g → 0`: the inclusion
of homology into `M₂ ⧸ range f` is exact at `M₂ ⧸ range f` with the map induced by `g`. -/
theorem exact_subtype_quotientRangeToRange (hfg : g ∘ₗ f = 0) :
    Function.Exact ((ker g).map (range f).mkQ).subtype (quotientRangeToRange hfg) := by
  rw [exact_iff, Submodule.range_subtype, ker_quotientRangeToRange]

/-- Homology is flat when the cokernel of the incoming map and the image of the outgoing map are
flat. -/
theorem flat_homology [Module.Flat R (M₂ ⧸ range f)] [Module.Flat R (range g)]
    (hfg : g ∘ₗ f = 0) : Module.Flat R ((ker g).map (range f).mkQ) :=
  (exact_subtype_quotientRangeToRange hfg).flat_left_of_injective_of_surjective
    (Submodule.injective_subtype _) (quotientRangeToRange_surjective hfg)

/-- Homology is finite when the cokernel of the incoming map is finite and the image of the
outgoing map is finitely presented. -/
theorem finite_homology [Module.Finite R (M₂ ⧸ range f)]
    [Module.FinitePresentation R (range g)] (hfg : g ∘ₗ f = 0) :
    Module.Finite R ((ker g).map (range f).mkQ) := by
  have hfg' := Module.FinitePresentation.fg_ker _ (quotientRangeToRange_surjective hfg)
  rw [(exact_subtype_quotientRangeToRange hfg).linearMap_ker_eq, Submodule.range_subtype]
    at hfg'
  exact Module.Finite.iff_fg.2 hfg'

/-- Homology is finitely presented when the cokernel of the incoming map is finitely presented and
the image of the outgoing map is projective. -/
theorem finitePresentation_homology [Module.FinitePresentation R (M₂ ⧸ range f)]
    [Module.Projective R (range g)] (hfg : g ∘ₗ f = 0) :
    Module.FinitePresentation R ((ker g).map (range f).mkQ) :=
  Module.finitePresentation_of_projective_of_exact _ _ (Submodule.injective_subtype _)
    (quotientRangeToRange_surjective hfg) (exact_subtype_quotientRangeToRange hfg)

/-- **The base change map on homology is surjective when the outgoing cokernel is flat.** For a
complex `M₁ → M₂ → M₃` with `M₃ ⧸ range g` flat, every homology class of
`S ⊗[R] M₁ → S ⊗[R] M₂ → S ⊗[R] M₃` comes from `S ⊗[R] H(M₁ → M₂ → M₃)`, for every `S`. -/
theorem homologyBaseChange_surjective [Module.Flat R (M₃ ⧸ range g)] (hfg : g ∘ₗ f = 0) :
    Function.Surjective (homologyBaseChange S f g) := by
  set ψ := (range f).liftQ g (range_le_ker_iff.2 hfg)
  have : Module.Flat R (M₃ ⧸ range ψ) := by rwa [Submodule.range_liftQ]
  rintro ⟨_, ⟨z, hz, rfl⟩⟩
  -- The class of `z` lies in the kernel of the base change of `ψ`, which is the base change of
  -- the kernel of `ψ` because `M₃ ⧸ range ψ` is flat.
  have hw : f.cokernelBaseChangeEquiv.symm ((range (f.baseChange S)).mkQ z) ∈
      (ker ψ).baseChange S := by
    rw [← ker_baseChange_of_flat_quotient_range, mem_ker]
    simpa using
      LinearMap.congr_fun (liftQ_baseChange_comp_cokernelBaseChangeEquiv_symm (S := S) hfg) z
        |>.trans (mem_ker.1 hz)
  rw [Submodule.ker_liftQ, Submodule.baseChange, mem_range] at hw
  obtain ⟨t, ht⟩ := hw
  refine ⟨t, Subtype.ext ?_⟩
  have := LinearMap.congr_fun (subtype_comp_homologyBaseChange S f g) t
  simp only [comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe] at this
  rw [this, ht, LinearEquiv.apply_symm_apply]

/-- **The base change map on homology is injective when the image of the outgoing map is
flat.** For a complex `M₁ → M₂ → M₃` with `range g` flat, the map
`S ⊗[R] H(M₁ → M₂ → M₃) → H(S ⊗[R] M₁ → S ⊗[R] M₂ → S ⊗[R] M₃)` is injective for every `S`. -/
theorem homologyBaseChange_injective [Module.Flat R (range g)] (hfg : g ∘ₗ f = 0) :
    Function.Injective (homologyBaseChange S f g) := by
  -- The inclusion of homology into `M₂ ⧸ range f` stays injective after base change because its
  -- cokernel `range g` is flat.
  have hinj := lTensor_injective_of_exact_of_flat _ (quotientRangeToRange_surjective hfg) _
    (Submodule.injective_subtype _) (exact_subtype_quotientRangeToRange hfg) S
  rw [← baseChange_eq_lTensor] at hinj
  intro x y hxy
  apply hinj
  have := congrArg (fun z ↦ f.cokernelBaseChangeEquiv.symm
    (((ker (g.baseChange S)).map (range (f.baseChange S)).mkQ).subtype z)) hxy
  simpa only [← comp_apply (Submodule.subtype _), subtype_comp_homologyBaseChange, comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using this

/-- **Homology commutes with every base change when the outgoing terms are flat.** For a complex
`M₁ → M₂ → M₃` with `M₃` and `M₃ ⧸ range g` flat, the base change map
`S ⊗[R] H(M₁ → M₂ → M₃) → H(S ⊗[R] M₁ → S ⊗[R] M₂ → S ⊗[R] M₃)` is bijective for every
`R`-algebra `S`. -/
theorem homologyBaseChange_bijective [Module.Flat R M₃] [Module.Flat R (M₃ ⧸ range g)]
    (hfg : g ∘ₗ f = 0) : Function.Bijective (homologyBaseChange S f g) := by
  have := (range g).flat_of_flat_quotient
  exact ⟨homologyBaseChange_injective S hfg, homologyBaseChange_surjective S hfg⟩

end LinearMap
