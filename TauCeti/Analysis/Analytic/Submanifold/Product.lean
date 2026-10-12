/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Basic
import TauCeti.Topology.Algebra.Module.Equiv.Fin
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Products of analytic submanifolds

The product of analytic submanifolds of dimensions `d` and `e` in `𝕜ⁿ` and `𝕜ᵐ`,
represented in `𝕜ⁿ⁺ᵐ` by concatenating coordinates, is an analytic submanifold of
dimension `d + e`. Analytic functions on the factors pull back along the two
coordinate projections, and their pairs are analytic on the product.

The product of two straightening charts initially has two separate blocks of
constrained coordinates. A continuous linear change of coordinates groups the
free coordinates of both factors first. Thus its image is the coordinate
subspace used by `IsAnalyticChart`, including when either factor has dimension
zero or full ambient dimension. Products supply parameter domains for analytic
families on submanifolds.

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second
  edition, Birkhäuser, 2002, Chapter 2.
-/

public section

noncomputable section

open Set Function

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n m d e : ℕ}

variable {S : Set (Fin n → 𝕜)} {T : Set (Fin m → 𝕜)}
  {c : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜)}
  {c' : OpenPartialHomeomorph (Fin m → 𝕜) (Fin m → 𝕜)}

/-- Construct a product chart, placing both factors' free coordinates first. -/
private theorem exists_product_chart (hd : d ≤ n) (he : e ≤ m)
    (hc : IsAnalyticChart d S c) (hc' : IsAnalyticChart e T c') :
    ∃ q : OpenPartialHomeomorph (Fin (n + m) → 𝕜) (Fin (n + m) → 𝕜),
      q.source = {x | (splitCoords (𝕜 := 𝕜) n m x).1 ∈ c.source ∧
        (splitCoords (𝕜 := 𝕜) n m x).2 ∈ c'.source} ∧
      IsAnalyticChart (d + e)
        {x | (splitCoords (𝕜 := 𝕜) n m x).1 ∈ S ∧ (splitCoords (𝕜 := 𝕜) n m x).2 ∈ T} q := by
  let A : (Fin (n + m) → 𝕜) ≃L[𝕜] (Fin n → 𝕜) × (Fin m → 𝕜) := splitCoords (𝕜 := 𝕜) n m
  let B := productCoords (𝕜 := 𝕜) (M := 𝕜) hd he
  let q := (A.toHomeomorph.transOpenPartialHomeomorph (c.prod c')).transHomeomorph
    B.toHomeomorph
  have hsource : q.source = {x | (A x).1 ∈ c.source ∧ (A x).2 ∈ c'.source} := by
    ext x
    simp [q]
  have htarget : q.target = {y | (B.symm y).1 ∈ c.target ∧ (B.symm y).2 ∈ c'.target} := by
    ext y
    simp [q]
  have hq (x) : q x = B (c (A x).1, c' (A x).2) := by
    simp [q]
  have hq' (y) : q.symm y = A.symm (c.symm (B.symm y).1, c'.symm (B.symm y).2) := by
    simp [q]
  refine ⟨q, hsource, ?_, ?_, ?_⟩
  · intro x hx
    rw [hsource] at hx
    have hpair : AnalyticAt 𝕜 (fun x ↦ (c (A x).1, c' (A x).2)) x :=
      ((hc.analyticOnNhd _ hx.1).fun_comp (f := fun x ↦ (A x).1)
        (analyticAt_fst.fun_comp (f := A) (A.analyticAt x))).prod
          ((hc'.analyticOnNhd _ hx.2).fun_comp (f := fun x ↦ (A x).2)
            (analyticAt_snd.fun_comp (f := A) (A.analyticAt x)))
    exact ((B.analyticAt _).comp hpair).congr (.of_forall fun x ↦ (hq x).symm)
  · intro y hy
    rw [htarget] at hy
    have hpair : AnalyticAt 𝕜 (fun y ↦ (c.symm (B.symm y).1, c'.symm (B.symm y).2)) y :=
      ((hc.analyticOnNhd_symm _ hy.1).fun_comp (f := fun y ↦ (B.symm y).1)
        (analyticAt_fst.fun_comp (f := B.symm) (B.symm.analyticAt y))).prod
          ((hc'.analyticOnNhd_symm _ hy.2).fun_comp (f := fun y ↦ (B.symm y).2)
            (analyticAt_snd.fun_comp (f := B.symm) (B.symm.analyticAt y)))
    exact ((A.symm.analyticAt _).comp hpair).congr (.of_forall fun y ↦ (hq' y).symm)
  · intro x hx
    rw [hsource] at hx
    simp only [mem_ofPred_eq, hq]
    rw [productCoords_vanishing_iff]
    exact (hc.mem_iff hx.1).symm.and (hc'.mem_iff hx.2).symm

/-- The product of `d`- and `e`-dimensional analytic submanifolds is an analytic submanifold
of dimension `d + e`. Its ambient coordinates are concatenated: the first `n` coordinates
belong to `S` and the final `m` to `T`. -/
theorem IsAnalyticSubmanifold.prod (hS : IsAnalyticSubmanifold d S)
    (hT : IsAnalyticSubmanifold e T) :
    IsAnalyticSubmanifold (d + e)
      {x : Fin (n + m) → 𝕜 | (fun i ↦ x (Fin.castAdd m i)) ∈ S ∧
        (fun i ↦ x (Fin.natAdd n i)) ∈ T} := by
  obtain ⟨s, hs⟩ := hS.nonempty
  obtain ⟨t, ht⟩ := hT.nonempty
  refine ⟨⟨Fin.append s t, by simpa using And.intro hs ht⟩,
    Nat.add_le_add hS.le hT.le, ?_⟩
  intro x hx
  obtain ⟨c, hxc, hc⟩ := hS.exists_isAnalyticChart _ hx.1
  obtain ⟨c', hxc', hc'⟩ := hT.exists_isAnalyticChart _ hx.2
  obtain ⟨q, hsource, hq⟩ := exists_product_chart hS.le hT.le hc hc'
  refine ⟨q, ?_, ?_⟩
  · simp only [hsource, mem_ofPred_eq, splitCoords_apply]
    exact ⟨hxc, hxc'⟩
  · simpa only [splitCoords_apply] using hq

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Functions analytic on the two factors combine into an analytic function on their product.
Only dimension bounds are needed: the functions already supply charts at every point, and
neither factor needs to be nonempty. -/
theorem AnalyticOnSubmanifold.prodMap {f : (Fin n → 𝕜) → E} {g : (Fin m → 𝕜) → F}
    (hf : AnalyticOnSubmanifold d f S) (hg : AnalyticOnSubmanifold e g T)
    (hd : d ≤ n) (he : e ≤ m) :
    AnalyticOnSubmanifold (d + e)
      (fun x : Fin (n + m) → 𝕜 ↦
        (f (fun i ↦ x (Fin.castAdd m i)), g (fun i ↦ x (Fin.natAdd n i))))
      {x | (fun i ↦ x (Fin.castAdd m i)) ∈ S ∧ (fun i ↦ x (Fin.natAdd n i)) ∈ T} := by
  rw [analyticOnSubmanifold_iff] at hf hg ⊢
  intro x hx
  obtain ⟨c, hxc, hc, hfc⟩ := hf _ hx.1
  obtain ⟨c', hxc', hc', hgc⟩ := hg _ hx.2
  obtain ⟨q, hsource, hq⟩ := exists_product_chart hd he hc hc'
  have hxq : x ∈ q.source := by
    simpa only [hsource, mem_ofPred_eq, splitCoords_apply] using And.intro hxc hxc'
  have hxST : x ∈ {x | (splitCoords (𝕜 := 𝕜) n m x).1 ∈ S ∧
      (splitCoords (𝕜 := 𝕜) n m x).2 ∈ T} := by
    simpa only [mem_ofPred_eq, splitCoords_apply] using hx
  let A : (Fin (n + m) → 𝕜) ≃L[𝕜] (Fin n → 𝕜) × (Fin m → 𝕜) := splitCoords (𝕜 := 𝕜) n m
  have hparam := (A.analyticAt _).fun_comp (hq.analyticAt_symm_firstCoords hxq hxST)
  have hbase := congrArg A (hq.symm_firstCoords_firstCoords_apply hxq hxST)
  have hmem := (hq.eventually_symm_firstCoords_mem hxq hxST).mono fun _ hu ↦ hu.2
  -- Recover the original point through the product chart before composing the two
  -- intrinsic coordinate expressions. No formula for the free-coordinate permutation is needed.
  have hleft := hc.analyticAt_comp (g := f) (analyticAt_fst.fun_comp hparam)
    (by simpa only [hbase, A, splitCoords_apply] using hxc)
    (hmem.mono fun _ hu ↦ hu.1) (by simpa only [hbase, A, splitCoords_apply] using hfc)
  have hright := hc'.analyticAt_comp (g := g) (analyticAt_snd.fun_comp hparam)
    (by simpa only [hbase, A, splitCoords_apply] using hxc')
    (hmem.mono fun _ hu ↦ hu.2) (by simpa only [hbase, A, splitCoords_apply] using hgc)
  refine ⟨q, hxq, ?_, ?_⟩
  · simpa only [splitCoords_apply] using hq
  · simpa only [Function.comp_def, A, splitCoords_apply] using hleft.prod hright

end TauCeti
