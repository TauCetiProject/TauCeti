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
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Smooth families of diffeomorphisms have jointly smooth inverses

Let `g : P × E → F` be `C^n`, with `1 ≤ n`, on an open set `S` of the product of a Banach space `P`
of parameters and a Banach space `E`. Suppose each slice `x ↦ g (p, x)` is injective on the
slice `{x | (p, x) ∈ S}` of `S`, with invertible derivative at every point of `S`. The inverse
function theorem then inverts the slices smoothly in the parameter as well: the map
`(p, y) ↦ (x ↦ g (p, x))⁻¹ y` is `C^n` on the image of `S` under `(p, x) ↦ (p, g (p, x))`
(`ContDiffOn.parametric_invFunOn`). When the slices with parameter in an open set `Ω` are
bijections, this gives that `(p, y) ↦ (x ↦ g (p, x))⁻¹ y` is `C^n` on `Ω ×ˢ univ`
(`ContDiffOn.parametric_invFun`). When `E = F` is finite-dimensional, an injective slice
derivative is invertible (`ContDiffOn.parametric_invFunOn_of_injective_fderiv`,
`ContDiffOn.parametric_invFun_of_injective_fderiv`).

The proof applies the inverse function theorem to the graph map `Φ (p, x) = (p, g (p, x))`. Its
derivative `(v, w) ↦ (v, dg (v, w))` is block triangular, with the identity and the slice
derivative on the diagonal, so it is invertible
(`ContinuousLinearMap.isInvertible_iff_of_fst_comp_eq`). The map `Φ` is injective on `S`, so its
inverse on `Φ '' S` is `C^n` by `IsLocalDiffeomorphOn.contMDiffOn_invFunOn`, and the inverses of
the slices are its second coordinate.

## Main results

* `ContDiffOn.parametric_invFunOn`: the inverses of a `C^n` family of injective maps between
  Banach spaces with invertible derivatives, on an open set, are jointly `C^n` in the parameter
  and the point.
* `ContDiffOn.parametric_invFun`: the same for a family of bijections indexed by an open set of
  parameters.
* `ContDiffOn.parametric_invFunOn_of_injective_fderiv`,
  `ContDiffOn.parametric_invFun_of_injective_fderiv`: the same for a finite-dimensional space,
  assuming only that the derivatives are injective.
-/

public section

noncomputable section

open Function Set
open scoped Manifold

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
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  -- The graph map `Φ (p, x) = (p, g (p, x))` of the family.
  set Φ : P × E → P × F := fun q ↦ (q.1, g q)
  have hΦ : ContDiffOn 𝕂 n Φ S := contDiffOn_fst.prodMk hg
  have hΦinj : InjOn Φ S := by
    rintro ⟨p, x⟩ hq ⟨p', x'⟩ hq' h
    obtain ⟨rfl, h⟩ := Prod.ext_iff.1 h
    exact Prod.ext rfl (hinj p hq hq' h)
  -- Its derivative `(v, w) ↦ (v, dg (v, 0) + dg (0, w))` is block triangular with invertible
  -- diagonal blocks, so `Φ` is a local diffeomorphism on `S`.
  have hΦloc : IsLocalDiffeomorphOn 𝓘(𝕂, P × E) 𝓘(𝕂, P × F) n Φ S := by
    rintro ⟨⟨p, x⟩, hq⟩
    have hgd := ((hg.differentiableOn hn0).differentiableAt (hS.mem_nhds hq)).hasFDerivAt
    have hΦd := (hasFDerivAt_fst (𝕜 := 𝕂) (p := (p, x))).prodMk hgd
    have hslice : fderiv 𝕂 (fun y ↦ g (p, y)) x =
        (fderiv 𝕂 g (p, x)).comp (ContinuousLinearMap.inr 𝕂 P E) :=
      (hgd.comp x (hasFDerivAt_prodMk_right p x)).fderiv
    have hfst : ContinuousLinearMap.fst 𝕂 P F ∘L fderiv 𝕂 Φ (p, x) =
        ContinuousLinearMap.fst 𝕂 P E := by
      rw [hΦd.fderiv]
      ext <;> simp
    obtain ⟨e, he⟩ := (ContinuousLinearMap.isInvertible_iff_of_fst_comp_eq hfst).2 <| by
      convert hinv (p, x) hq using 1
      rw [hΦd.fderiv, hslice]
      ext; simp
    exact TauCeti.isLocalDiffeomorphAt_of_fderiv_eq hΦ hS hq hn he
  have hinvC : ContDiffOn 𝕂 n (invFunOn Φ S) (Φ '' S) :=
    contMDiffOn_iff_contDiffOn.1 (hΦloc.contMDiffOn_invFunOn hS hΦinj)
  refine (contDiff_snd.comp_contDiffOn hinvC).congr fun q hq ↦ ?_
  -- The second coordinate of `Φ⁻¹ (p, y)` is the preimage of `y` under the slice at `p`.
  have hmem := invFunOn_mem hq
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 (invFunOn_eq hq : Φ (invFunOn Φ S q) = q)
  set r := invFunOn Φ S q
  have hr : r = (q.1, r.2) := Prod.ext h1 rfl
  have hmem' : r.2 ∈ Prod.mk q.1 ⁻¹' S := by rw [mem_preimage, ← hr]; exact hmem
  have hy : g (q.1, r.2) = q.2 := by rw [← hr]; exact h2
  simp only [comp_apply]
  rw [← hy]
  exact (hinj q.1).leftInvOn_invFunOn hmem'

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
inverses.** A variant of `ContDiffOn.parametric_invFunOn` for finite-dimensional `F`, where an
injective slice derivative is automatically invertible. -/
theorem ContDiffOn.parametric_invFunOn_of_injective_fderiv [FiniteDimensional 𝕂 F]
    {g : P × F → F} {S : Set (P × F)} (hg : ContDiffOn 𝕂 n g S) (hS : IsOpen S) (hn : 1 ≤ n)
    (hinj : ∀ p, InjOn (fun x ↦ g (p, x)) (Prod.mk p ⁻¹' S))
    (hinjd : ∀ q ∈ S, Injective (fderiv 𝕂 (fun x ↦ g (q.1, x)) q.2)) :
    ContDiffOn 𝕂 n (fun q : P × F ↦ invFunOn (fun x ↦ g (q.1, x)) (Prod.mk q.1 ⁻¹' S) q.2)
      ((fun q ↦ (q.1, g q)) '' S) :=
  have : CompleteSpace F := FiniteDimensional.completeSpace 𝕂 F
  hg.parametric_invFunOn hS hn hinj fun q hq ↦
    ⟨(LinearEquiv.ofInjectiveEndo _ (hinjd q hq)).toContinuousLinearEquiv, rfl⟩

/-- **Smooth families of diffeomorphisms of a finite-dimensional space have jointly smooth
inverses.** A variant of `ContDiffOn.parametric_invFun` for finite-dimensional `F`, where an
injective slice derivative is automatically invertible. -/
theorem ContDiffOn.parametric_invFun_of_injective_fderiv [FiniteDimensional 𝕂 F]
    {g : P × F → F} (hg : ContDiffOn 𝕂 n g (Ω ×ˢ univ)) (hΩ : IsOpen Ω) (hn : 1 ≤ n)
    (hbij : ∀ p ∈ Ω, Bijective fun x ↦ g (p, x))
    (hinjd : ∀ p ∈ Ω, ∀ x, Injective (fderiv 𝕂 (fun x ↦ g (p, x)) x)) :
    ContDiffOn 𝕂 n (fun q : P × F ↦ invFun (fun x ↦ g (q.1, x)) q.2) (Ω ×ˢ univ) :=
  have : CompleteSpace F := FiniteDimensional.completeSpace 𝕂 F
  hg.parametric_invFun hΩ hn hbij fun p hp x ↦
    ⟨(LinearEquiv.ofInjectiveEndo _ (hinjd p hp x)).toContinuousLinearEquiv, rfl⟩
