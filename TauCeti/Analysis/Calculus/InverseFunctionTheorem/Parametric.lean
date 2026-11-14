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
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

/-!
# Smooth families of diffeomorphisms have jointly smooth inverses

Let `g : P × F → F` be `C^n`, with `1 ≤ n`, on `Ω ×ˢ univ` for an open set `Ω` of parameters in a
Banach space `P`, and suppose each slice `x ↦ g (p, x)` with `p ∈ Ω` is a bijection of the Banach
space `F` with invertible derivative. The inverse function theorem then inverts the slices
smoothly in the parameter as well: the map `(p, y) ↦ (x ↦ g (p, x))⁻¹ y` is `C^n` on `Ω ×ˢ univ`
(`ContDiffOn.parametric_invFun`). When `F` is finite-dimensional, an injective slice derivative
is invertible (`ContDiffOn.parametric_invFun_of_injective`).

The proof applies the inverse function theorem to the graph map `Φ (p, x) = (p, g (p, x))`. Its
derivative `(v, w) ↦ (v, dg (v, w))` is block triangular, with the identity and the slice
derivative on the diagonal, so it is invertible (`ContinuousLinearEquiv.skewProd`). The map `Φ` is
injective on `Ω ×ˢ univ`, so its inverse there is `C^n` by
`IsLocalDiffeomorphOn.contMDiffOn_invFunOn`, and the inverses of the slices are its second
coordinate.

## Main results

* `ContDiffOn.parametric_invFun`: the inverses of a `C^n` family of diffeomorphisms of a Banach
  space with invertible derivatives are jointly `C^n` in the parameter and the point.
* `ContDiffOn.parametric_invFun_of_injective`: the same for a finite-dimensional space, assuming
  only that the derivatives are injective.
-/

public section

noncomputable section

open Function Set
open scoped Manifold

variable {𝕂 : Type*} [RCLike 𝕂] {n : WithTop ℕ∞} {P F : Type*} [NormedAddCommGroup P]
  [NormedSpace 𝕂 P] [CompleteSpace P] [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  {g : P × F → F} {Ω : Set P}

/-- **Smooth families of diffeomorphisms have jointly smooth inverses.** Let `g : P × F → F` be
`C^n` on `Ω ×ˢ univ`, with `Ω` open in the Banach space `P` and `1 ≤ n`, such that for every
`p ∈ Ω` the slice `x ↦ g (p, x)` is a bijection of the Banach space `F` with invertible derivative
everywhere. Then the inverses of the slices, `(p, y) ↦ (x ↦ g (p, x))⁻¹ y`, form a `C^n` function
on `Ω ×ˢ univ`. -/
theorem ContDiffOn.parametric_invFun [CompleteSpace F] (hg : ContDiffOn 𝕂 n g (Ω ×ˢ univ))
    (hΩ : IsOpen Ω) (hn : 1 ≤ n) (hbij : ∀ p ∈ Ω, Bijective fun x ↦ g (p, x))
    (hinv : ∀ p ∈ Ω, ∀ x, (fderiv 𝕂 (fun x ↦ g (p, x)) x).IsInvertible) :
    ContDiffOn 𝕂 n (fun q : P × F ↦ invFun (fun x ↦ g (q.1, x)) q.2) (Ω ×ˢ univ) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  set S : Set (P × F) := Ω ×ˢ univ
  have hS : IsOpen S := hΩ.prod isOpen_univ
  -- The graph map `Φ (p, x) = (p, g (p, x))` of the family.
  set Φ : P × F → P × F := fun q ↦ (q.1, g q)
  have hΦ : ContDiffOn 𝕂 n Φ S := contDiffOn_fst.prodMk hg
  have hΦinj : InjOn Φ S := by
    rintro ⟨p, x⟩ hq ⟨p', x'⟩ - h
    obtain ⟨rfl, h⟩ := Prod.ext_iff.1 h
    exact Prod.ext rfl ((hbij p hq.1).1 h)
  -- Its derivative `(v, w) ↦ (v, dg (v, 0) + dg (0, w))` is block triangular with invertible
  -- diagonal blocks, so `Φ` is a local diffeomorphism on `S`.
  have hΦloc : IsLocalDiffeomorphOn 𝓘(𝕂, P × F) 𝓘(𝕂, P × F) n Φ S := by
    rintro ⟨⟨p, x⟩, hq⟩
    have hgd := ((hg.differentiableOn hn0).differentiableAt (hS.mem_nhds hq)).hasFDerivAt
    have hΦd := (hasFDerivAt_fst (𝕜 := 𝕂) (p := (p, x))).prodMk hgd
    have hslice : fderiv 𝕂 (fun y ↦ g (p, y)) x =
        (fderiv 𝕂 g (p, x)).comp (ContinuousLinearMap.inr 𝕂 P F) :=
      (hgd.comp x (hasFDerivAt_prodMk_right p x)).fderiv
    obtain ⟨e, he⟩ := hinv p hq.1 x
    have he' (w : F) : e w = fderiv 𝕂 g (p, x) (0, w) := by
      rw [← ContinuousLinearEquiv.coe_coe, he, hslice]
      rfl
    refine TauCeti.isLocalDiffeomorphAt_of_fderiv_eq hΦ hS hq hn
      (e := (ContinuousLinearEquiv.refl 𝕂 P).skewProd e
        ((fderiv 𝕂 g (p, x)).comp (ContinuousLinearMap.inl 𝕂 P F))) ?_
    rw [hΦd.fderiv]
    ext v <;> simp [he', ← Prod.zero_eq_mk]
  have hsurj : S ⊆ Φ '' S := by
    rintro ⟨p, y⟩ hq
    obtain ⟨x, hx⟩ := (hbij p hq.1).2 y
    exact ⟨(p, x), ⟨hq.1, mem_univ x⟩, Prod.ext rfl hx⟩
  have hinvC : ContDiffOn 𝕂 n (invFunOn Φ S) S :=
    (contMDiffOn_iff_contDiffOn.1 (hΦloc.contMDiffOn_invFunOn hS hΦinj)).mono hsurj
  refine (contDiff_snd.comp_contDiffOn hinvC).congr fun q hq ↦ ?_
  -- The second coordinate of `Φ⁻¹ (p, y)` is the preimage of `y` under the slice at `p`.
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 (invFunOn_eq (hsurj hq) : Φ (invFunOn Φ S q) = q)
  refine (hbij q.1 hq.1).1 ?_
  simp only [comp_apply]
  rw [invFun_eq ((hbij q.1 hq.1).2 q.2)]
  conv_rhs => rw [← h1]
  exact h2.symm

/-- **Smooth families of diffeomorphisms of a finite-dimensional space have jointly smooth
inverses.** A variant of `ContDiffOn.parametric_invFun` for finite-dimensional `F`, where an
injective slice derivative is automatically invertible. -/
theorem ContDiffOn.parametric_invFun_of_injective [FiniteDimensional 𝕂 F]
    (hg : ContDiffOn 𝕂 n g (Ω ×ˢ univ)) (hΩ : IsOpen Ω) (hn : 1 ≤ n)
    (hbij : ∀ p ∈ Ω, Bijective fun x ↦ g (p, x))
    (hinj : ∀ p ∈ Ω, ∀ x, Injective (fderiv 𝕂 (fun x ↦ g (p, x)) x)) :
    ContDiffOn 𝕂 n (fun q : P × F ↦ invFun (fun x ↦ g (q.1, x)) q.2) (Ω ×ˢ univ) :=
  have : CompleteSpace F := FiniteDimensional.completeSpace 𝕂 F
  hg.parametric_invFun hΩ hn hbij fun p hp x ↦
    ⟨(LinearEquiv.ofInjectiveEndo _ (hinj p hp x)).toContinuousLinearEquiv, rfl⟩
