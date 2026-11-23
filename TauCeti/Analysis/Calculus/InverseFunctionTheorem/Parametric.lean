/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.JointImplicitFunction
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Smooth families of diffeomorphisms have jointly smooth inverses

Let `g : P × E → F` be `C^n`, with `1 ≤ n`, on an open set `S` of the product of a Banach space `P`
of parameters and a Banach space `E`. Suppose each slice `x ↦ g (p, x)` is injective on the
slice `{x | (p, x) ∈ S}` of `S`, with invertible derivative at every point of `S`. The inverse
function theorem then inverts the slices smoothly in the parameter as well: the map
`(p, y) ↦ (x ↦ g (p, x))⁻¹ y` is `C^n` on the image of `S` under `(p, x) ↦ (p, g (p, x))`
(`ContDiffOn.parametric_invFunOn`). When the slices with parameter in an open set `Ω` are
bijections, this gives that `(p, y) ↦ (x ↦ g (p, x))⁻¹ y` is `C^n` on `Ω ×ˢ univ`
(`ContDiffOn.parametric_invFun`). When `E` and `F` are finite-dimensional of the same dimension,
an injective slice derivative is invertible (`ContDiffOn.parametric_invFunOn_of_injective_fderiv`,
`ContDiffOn.parametric_invFun_of_injective_fderiv`).

Near each point `(p, g (p, x))` with `(p, x) ∈ S`, the inverses of the slices agree with the joint
implicit function of `g` at `(p, x)`, which solves `g (p', ψ (p', y)) = y` and is `C^n`
(`HasStrictFDerivAt.contDiffAt_jointImplicitFunctionOfProdDomain`). The agreement is the local
uniqueness of the joint implicit function
(`HasStrictFDerivAt.eventuallyEq_jointImplicitFunctionOfProdDomain`), since the inverses undo
`g` on the open set `S`.

## Main results

* `ContDiffOn.parametric_invFunOn`: the inverses of a `C^n` family of injective maps between
  Banach spaces with invertible derivatives, on an open set, are jointly `C^n` in the parameter
  and the point.
* `ContDiffOn.parametric_invFun`: the same for a family of bijections indexed by an open set of
  parameters.
* `ContDiffOn.parametric_invFunOn_of_injective_fderiv`,
  `ContDiffOn.parametric_invFun_of_injective_fderiv`: the same for finite-dimensional spaces of
  the same dimension, assuming only that the derivatives are injective.
-/

public section

noncomputable section

open Function Set

variable {𝕂 : Type*} [RCLike 𝕂] {n : WithTop ℕ∞} {P E F : Type*} [NormedAddCommGroup P]
  [NormedSpace 𝕂 P] [CompleteSpace P] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  [NormedAddCommGroup F] [NormedSpace 𝕂 F] {Ω : Set P}

/-- **Smooth families of local diffeomorphisms have jointly smooth inverses.** Let
`g : P × E → F` be `C^n` on an open set `S` of `P × E`, with `P` and `E` Banach spaces and
`1 ≤ n`, such that every slice `x ↦ g (p, x)` is injective on `{x | (p, x) ∈ S}` and has
invertible derivative at every `x` with `(p, x) ∈ S`. Then the inverses of the slices on these
sets, `(p, y) ↦ (x ↦ g (p, x))⁻¹ y`, form a `C^n` function on the image of `S` under
`(p, x) ↦ (p, g (p, x))`. -/
theorem ContDiffOn.parametric_invFunOn [CompleteSpace E] {g : P × E → F} {S : Set (P × E)}
    (hg : ContDiffOn 𝕂 n g S) (hS : IsOpen S) (hn : 1 ≤ n)
    (hinj : ∀ p, InjOn (fun x ↦ g (p, x)) (Prod.mk p ⁻¹' S))
    (hinv : ∀ q ∈ S, (fderiv 𝕂 (fun x ↦ g (q.1, x)) q.2).IsInvertible) :
    ContDiffOn 𝕂 n (fun q : P × F ↦ invFunOn (fun x ↦ g (q.1, x)) (Prod.mk q.1 ⁻¹' S) q.2)
      ((fun q ↦ (q.1, g q)) '' S) := by
  rintro _ ⟨⟨p, x⟩, hq, rfl⟩
  have hgq : ContDiffAt 𝕂 n g (p, x) := hg.contDiffAt (hS.mem_nhds hq)
  have hn0 : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.1 hn
  have dgq := hgq.hasStrictFDerivAt_fderiv hn0
  -- The slice derivative at `x` is the second partial derivative of `g` at `(p, x)`.
  have hinvq : (fderiv 𝕂 g (p, x) ∘L .inr 𝕂 P E).IsInvertible := by
    rw [← TauCeti.fderiv_slice_right (hgq.differentiableAt hn0)]
    exact hinv (p, x) hq
  obtain ⟨e, he⟩ := hinvq
  have : CompleteSpace F :=
    ContinuousLinearMap.completeSpace_of_isInvertible (f := (e.symm : F →L[𝕂] E)) ⟨e.symm, rfl⟩
  -- Near `(p, g (p, x))`, the inverses of the slices are the joint implicit function of `g`.
  refine ((dgq.contDiffAt_jointImplicitFunctionOfProdDomain ⟨e, he⟩ hgq).congr_of_eventuallyEq
    (dgq.eventuallyEq_jointImplicitFunctionOfProdDomain ⟨e, he⟩ ?_)).contDiffWithinAt
  filter_upwards [hS.mem_nhds hq] with v hv
  exact (hinj v.1).leftInvOn_invFunOn (x := v.2) hv

/-- **Smooth families of diffeomorphisms have jointly smooth inverses.** Let `g : P × E → F` be
`C^n` on `Ω ×ˢ univ`, with `Ω` open in the Banach space `P`, `E` a Banach space and `1 ≤ n`, such
that for every `p ∈ Ω` the slice `x ↦ g (p, x)` is a bijection with invertible derivative
everywhere. Then the inverses of the slices, `(p, y) ↦ (x ↦ g (p, x))⁻¹ y`, form a `C^n` function
on `Ω ×ˢ univ`. -/
theorem ContDiffOn.parametric_invFun [CompleteSpace E] {g : P × E → F}
    (hg : ContDiffOn 𝕂 n g (Ω ×ˢ univ)) (hΩ : IsOpen Ω) (hn : 1 ≤ n)
    (hbij : ∀ p ∈ Ω, Bijective fun x ↦ g (p, x))
    (hinv : ∀ p ∈ Ω, ∀ x, (fderiv 𝕂 (fun x ↦ g (p, x)) x).IsInvertible) :
    ContDiffOn 𝕂 n (fun q : P × F ↦ invFun (fun x ↦ g (q.1, x)) q.2) (Ω ×ˢ univ) := by
  have h := hg.parametric_invFunOn (hΩ.prod isOpen_univ) hn
    (fun p x hx _ _ hxx' ↦ (hbij p hx.1).1 hxx') fun q hq ↦ hinv q.1 hq.1 q.2
  have hsurj : Ω ×ˢ (univ : Set F) ⊆ (fun q ↦ (q.1, g q)) '' (Ω ×ˢ univ) := by
    rintro ⟨p, y⟩ hq
    obtain ⟨x, hx⟩ := (hbij p hq.1).2 y
    exact ⟨(p, x), ⟨hq.1, mem_univ x⟩, Prod.ext rfl hx⟩
  refine (h.mono hsurj).congr fun q hq ↦ (hbij q.1 hq.1).1 ?_
  obtain ⟨x, hx⟩ := (hbij q.1 hq.1).2 q.2
  exact (invFun_eq (f := fun x ↦ g (q.1, x)) ⟨x, hx⟩).trans
    (invFunOn_eq (f := fun x ↦ g (q.1, x)) (s := Prod.mk q.1 ⁻¹' (Ω ×ˢ univ))
      ⟨x, ⟨hq.1, mem_univ x⟩, hx⟩).symm

/-- **Smooth families of local diffeomorphisms of a finite-dimensional space have jointly smooth
inverses.** A variant of `ContDiffOn.parametric_invFunOn` for finite-dimensional `E` and `F` of the
same dimension, where an injective slice derivative is automatically invertible. -/
theorem ContDiffOn.parametric_invFunOn_of_injective_fderiv [FiniteDimensional 𝕂 E]
    [FiniteDimensional 𝕂 F] {g : P × E → F} {S : Set (P × E)} (hg : ContDiffOn 𝕂 n g S)
    (hS : IsOpen S) (hn : 1 ≤ n) (hinj : ∀ p, InjOn (fun x ↦ g (p, x)) (Prod.mk p ⁻¹' S))
    (hinjd : ∀ q ∈ S, Injective (fderiv 𝕂 (fun x ↦ g (q.1, x)) q.2))
    (hdim : Module.finrank 𝕂 E = Module.finrank 𝕂 F) :
    ContDiffOn 𝕂 n (fun q : P × F ↦ invFunOn (fun x ↦ g (q.1, x)) (Prod.mk q.1 ⁻¹' S) q.2)
      ((fun q ↦ (q.1, g q)) '' S) :=
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕂 E
  hg.parametric_invFunOn hS hn hinj fun q hq ↦
    (ContinuousLinearMap.isInvertible_iff_injective_of_finrank_eq hdim).2 (hinjd q hq)

/-- **Smooth families of diffeomorphisms of a finite-dimensional space have jointly smooth
inverses.** A variant of `ContDiffOn.parametric_invFun` for finite-dimensional `E` and `F` of the
same dimension, where an injective slice derivative is automatically invertible. -/
theorem ContDiffOn.parametric_invFun_of_injective_fderiv [FiniteDimensional 𝕂 E]
    [FiniteDimensional 𝕂 F] {g : P × E → F} (hg : ContDiffOn 𝕂 n g (Ω ×ˢ univ)) (hΩ : IsOpen Ω)
    (hn : 1 ≤ n) (hbij : ∀ p ∈ Ω, Bijective fun x ↦ g (p, x))
    (hinjd : ∀ p ∈ Ω, ∀ x, Injective (fderiv 𝕂 (fun x ↦ g (p, x)) x))
    (hdim : Module.finrank 𝕂 E = Module.finrank 𝕂 F) :
    ContDiffOn 𝕂 n (fun q : P × F ↦ invFun (fun x ↦ g (q.1, x)) q.2) (Ω ×ˢ univ) :=
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕂 E
  hg.parametric_invFun hΩ hn hbij fun p hp x ↦
    (ContinuousLinearMap.isInvertible_iff_injective_of_finrank_eq hdim).2 (hinjd p hp x)
