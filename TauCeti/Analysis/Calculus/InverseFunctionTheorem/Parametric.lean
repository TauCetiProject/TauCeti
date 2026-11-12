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

Let `g : P × F → F` be `C^n`, with `1 ≤ n`, on `Ω ×ˢ univ` for an open set `Ω` of parameters, and
suppose each slice `x ↦ g (p, x)` with `p ∈ Ω` is a bijection of `F` with injective derivative. In
finite dimensions the inverse function theorem then inverts the slices smoothly in the parameter
as well: the map `(p, y) ↦ (x ↦ g (p, x))⁻¹ y` is `C^n` on `Ω ×ˢ univ`
(`ContDiffOn.parametric_invFun`).

The proof applies the inverse function theorem to the graph map `Φ (p, x) = (p, g (p, x))`. Its
derivative `(v, w) ↦ (v, dg (v, w))` is block triangular, with the slice derivative on the
diagonal, so it is injective and hence invertible. The map `Φ` is injective on `Ω ×ˢ univ`, so its
inverse there is `C^n` by `IsLocalDiffeomorphOn.contMDiffOn_invFunOn`, and the inverses of the
slices are its second coordinate.

## Main results

* `ContDiffOn.parametric_invFun`: the inverses of a `C^n` family of diffeomorphisms of a
  finite-dimensional space are jointly `C^n` in the parameter and the point.
-/

public section

noncomputable section

open Function Set
open scoped Manifold

variable {𝕂 : Type*} [RCLike 𝕂] {n : WithTop ℕ∞}

/-- **Smooth families of diffeomorphisms have jointly smooth inverses.** Let `g : P × F → F` be
`C^n` on `Ω ×ˢ univ`, with `Ω` open and `1 ≤ n`, such that for every `p ∈ Ω` the slice
`x ↦ g (p, x)` is bijective with injective derivative everywhere. Then the inverses of the slices,
`(p, y) ↦ (x ↦ g (p, x))⁻¹ y`, form a `C^n` function on `Ω ×ˢ univ`. -/
theorem ContDiffOn.parametric_invFun {P F : Type*} [NormedAddCommGroup P] [NormedSpace 𝕂 P]
    [FiniteDimensional 𝕂 P] [NormedAddCommGroup F] [NormedSpace 𝕂 F] [FiniteDimensional 𝕂 F]
    {g : P × F → F} {Ω : Set P} (hg : ContDiffOn 𝕂 n g (Ω ×ˢ univ)) (hΩ : IsOpen Ω)
    (hn : 1 ≤ n) (hbij : ∀ p ∈ Ω, Bijective fun x ↦ g (p, x))
    (hinj : ∀ p ∈ Ω, ∀ x, Injective (fderiv 𝕂 (fun x ↦ g (p, x)) x)) :
    ContDiffOn 𝕂 n (fun q : P × F ↦ invFun (fun x ↦ g (q.1, x)) q.2) (Ω ×ˢ univ) := by
  have : CompleteSpace P := FiniteDimensional.complete 𝕂 P
  have : CompleteSpace F := FiniteDimensional.complete 𝕂 F
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
  -- Its derivative `(v, w) ↦ (v, dg (v, w))` is injective, hence invertible, so `Φ` is a local
  -- diffeomorphism on `S`.
  have hΦloc : IsLocalDiffeomorphOn 𝓘(𝕂, P × F) 𝓘(𝕂, P × F) n Φ S := by
    rintro ⟨⟨p, x⟩, hq⟩
    have hgd := ((hg.differentiableOn hn0).differentiableAt (hS.mem_nhds hq)).hasFDerivAt
    have hΦd := (hasFDerivAt_fst (𝕜 := 𝕂) (p := (p, x))).prodMk hgd
    have hslice : fderiv 𝕂 (fun y ↦ g (p, y)) x =
        (fderiv 𝕂 g (p, x)).comp (ContinuousLinearMap.inr 𝕂 P F) :=
      (hgd.comp x (hasFDerivAt_prodMk_right p x)).fderiv
    have hinj' : Injective (fderiv 𝕂 Φ (p, x)) := by
      rw [hΦd.fderiv]
      rintro ⟨v, w⟩ ⟨v', w'⟩ h
      obtain rfl : v = v' := by simpa using congrArg Prod.fst h
      replace h : fderiv 𝕂 g (p, x) (v, w) = fderiv 𝕂 g (p, x) (v, w') := by
        simpa using congrArg Prod.snd h
      refine Prod.ext rfl (hinj p hq.1 x ?_)
      have hw : ∀ u : F, ((v, u) : P × F) = (v, 0) + (0, u) := fun u ↦ by simp
      rw [hw w, hw w', map_add, map_add] at h
      simpa [hslice] using add_left_cancel h
    exact TauCeti.isLocalDiffeomorphAt_of_fderiv_eq hΦ hS hq hn
      (e := (LinearEquiv.ofInjectiveEndo (fderiv 𝕂 Φ (p, x)).toLinearMap
        hinj').toContinuousLinearEquiv) rfl
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
