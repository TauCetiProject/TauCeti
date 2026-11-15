/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.SpanRank
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Torsion
public import TauCeti.Topology.Algebra.Group.Profinite.Rank
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# The rank of an abelian pro-`p` group as a `ℤ_p`-module

An abelian pro-`p` group `A` is a compact `ℤ_[p]`-module through `p`-adic exponentiation,
`TauCeti.IsProP.module`, and a finite subset topologically generates `A` exactly when it spans
that module (`TauCeti.IsProP.topologicalClosure_closure_eq_top_iff_span_eq_top`). This file draws
the numerical consequence: when `A` is topologically finitely generated, its topological generator
rank `d(A)` is the least number of generators of the `ℤ_[p]`-module, `Submodule.spanFinrank`. When
`A` is moreover torsion-free the module is free, and `d(A)` is its `ℤ_[p]`-rank.

The basic example is `ℤ_p` itself: its canonical module structure is that of the ring `ℤ_[p]`, so
it is the free `ℤ_[p]`-module of rank one. Together with the identification of `ℤ_p` with the free
pro-`p` group on one generator, `TauCeti.freeProP.equivPadicInt`, this is the module-theoretic form
of the statement that `ℤ_p` is the pro-`p` completion of `ℤ`.

## Main results

* `TauCeti.IsProP.topologicalGeneratorRankNat_eq_spanFinrank`: for a topologically finitely
  generated abelian pro-`p` group, the topological generator rank is the span rank of the
  canonical `ℤ_[p]`-module.
* `TauCeti.IsProP.topologicalGeneratorRankNat_eq_finrank`: if the group is moreover
  torsion-free, the topological generator rank is the `ℤ_[p]`-rank.
* `TauCeti.additiveMultiplicativePadicIntEquiv`: the canonical `ℤ_[p]`-module structure on `ℤ_p`
  is that of the ring `ℤ_[p]`.
* `TauCeti.free_module_multiplicative_padicInt`,
  `TauCeti.finrank_module_multiplicative_padicInt`: `ℤ_p` is the free `ℤ_[p]`-module of rank one.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 4.3.
-/

public section

namespace TauCeti

namespace IsProP

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommGroup A] [TopologicalSpace A]
  [IsTopologicalGroup A] [CompactSpace A] [TotallyDisconnectedSpace A]

/-- **The two notions of rank of an abelian pro-`p` group agree.** For a topologically finitely
generated abelian pro-`p` group, the least number of topological generators is the least number
of generators of the canonical `ℤ_[p]`-module `TauCeti.IsProP.module`. -/
theorem topologicalGeneratorRankNat_eq_spanFinrank (hA : IsProP p A)
    (hfg : IsTopologicallyFinitelyGenerated A) :
    letI := hA.module
    topologicalGeneratorRankNat A hfg = (⊤ : Submodule ℤ_[p] (Additive A)).spanFinrank := by
  let _ : Module ℤ_[p] (Additive A) := hA.module
  have hfin := hA.isTopologicallyFinitelyGenerated_iff_module_finite.mp hfg
  refine le_antisymm ?_ ?_
  · obtain ⟨t, htcard, ht⟩ := hfin.fg_top.exists_span_finset_card_eq_spanFinrank
    classical
    refine (topologicalGeneratorRankNat_le hfg (s := t.image Additive.toMul) ?_).trans
      (htcard ▸ Finset.card_image_le)
    rwa [hA.topologicalClosure_closure_eq_top_iff_span_eq_top (Finset.finite_toSet _),
      Finset.coe_image, Additive.toMul.injective.preimage_image]
  · obtain ⟨s, hscard, hs⟩ := exists_finset_card_eq_topologicalGeneratorRankNat hfg
    rw [hA.topologicalClosure_closure_eq_top_iff_span_eq_top s.finite_toSet] at hs
    rw [← hs, ← hscard, ← Set.ncard_coe_finset,
      ← Set.ncard_preimage_of_injective_subset_range Additive.toMul.injective
        (by simp [Additive.toMul.surjective.range_eq])]
    exact Submodule.spanFinrank_span_le_ncard_of_finite
      (s.finite_toSet.preimage Additive.toMul.injective.injOn)

/-- **The topological generator rank of a torsion-free abelian pro-`p` group is its `ℤ_p`-rank.**
A topologically finitely generated torsion-free abelian pro-`p` group is a free module over
`ℤ_[p]`, for the canonical structure `TauCeti.IsProP.module`, and the least number of its
topological generators is the rank of that free module. -/
theorem topologicalGeneratorRankNat_eq_finrank [IsMulTorsionFree A] (hA : IsProP p A)
    (hfg : IsTopologicallyFinitelyGenerated A) :
    letI := hA.module
    topologicalGeneratorRankNat A hfg = Module.finrank ℤ_[p] (Additive A) := by
  let _ : Module ℤ_[p] (Additive A) := hA.module
  have := hA.isTopologicallyFinitelyGenerated_iff_module_finite.mp hfg
  have := hA.isTorsionFree_module_iff.mpr ‹_›
  rw [Module.finrank_eq_spanFinrank_of_free, hA.topologicalGeneratorRankNat_eq_spanFinrank hfg]

end IsProP

section PadicInt

open Multiplicative

variable (p : ℕ) [Fact p.Prime]

/-- **The canonical `ℤ_[p]`-module structure on `ℤ_p` is that of the ring `ℤ_[p]`.** The additive
group `ℤ_[p]`, written multiplicatively, is pro-`p`, and for its canonical module structure
`TauCeti.IsProP.module` the identity of the underlying additive groups is a continuous
`ℤ_[p]`-linear equivalence with `ℤ_[p]`. -/
noncomputable def additiveMultiplicativePadicIntEquiv :
    letI := (isProP_multiplicative_padicInt p).module
    Additive (Multiplicative ℤ_[p]) ≃L[ℤ_[p]] ℤ_[p] :=
  letI := (isProP_multiplicative_padicInt p).module
  haveI := (isProP_multiplicative_padicInt p).continuousSMul_module
  -- A continuous additive isomorphism of topological `ℤ_[p]`-modules is automatically linear.
  (AddEquiv.additiveMultiplicative ℤ_[p]).toPadicIntLinearEquiv p continuous_id continuous_id

@[simp]
theorem additiveMultiplicativePadicIntEquiv_apply (x : Additive (Multiplicative ℤ_[p])) :
    additiveMultiplicativePadicIntEquiv p x = x.toMul.toAdd :=
  letI := (isProP_multiplicative_padicInt p).module
  haveI := (isProP_multiplicative_padicInt p).continuousSMul_module
  congrFun (AddEquiv.coe_toPadicIntLinearEquiv p _ _ _) x

@[simp]
theorem additiveMultiplicativePadicIntEquiv_symm_apply (l : ℤ_[p]) :
    letI := (isProP_multiplicative_padicInt p).module
    (additiveMultiplicativePadicIntEquiv p).symm l = Additive.ofMul (ofAdd l) :=
  letI := (isProP_multiplicative_padicInt p).module
  haveI := (isProP_multiplicative_padicInt p).continuousSMul_module
  congrFun (AddEquiv.coe_toPadicIntLinearEquiv_symm p _ _ _) l

/-- **`ℤ_p` is a free `ℤ_[p]`-module** for its canonical module structure
`TauCeti.IsProP.module`. -/
theorem free_module_multiplicative_padicInt :
    letI := (isProP_multiplicative_padicInt p).module
    Module.Free ℤ_[p] (Additive (Multiplicative ℤ_[p])) :=
  letI := (isProP_multiplicative_padicInt p).module
  Module.Free.of_equiv (additiveMultiplicativePadicIntEquiv p).symm.toLinearEquiv

/-- **`ℤ_p` has rank one as a `ℤ_[p]`-module** for its canonical module structure
`TauCeti.IsProP.module`. -/
theorem finrank_module_multiplicative_padicInt :
    letI := (isProP_multiplicative_padicInt p).module
    Module.finrank ℤ_[p] (Additive (Multiplicative ℤ_[p])) = 1 :=
  letI := (isProP_multiplicative_padicInt p).module
  (additiveMultiplicativePadicIntEquiv p).toLinearEquiv.finrank_eq.trans (Module.finrank_self ℤ_[p])

end PadicInt

end TauCeti
