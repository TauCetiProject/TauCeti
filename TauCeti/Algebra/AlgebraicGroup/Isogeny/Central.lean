/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.FiniteEtale
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Connected affine isogenies with geometrically reduced kernel are central

An isogeny with geometrically reduced kernel from a geometrically reduced, geometrically
connected finite-type affine group is central. The kernel is finite and normal, so the
finite normal-subgroup centrality theorem applies. In particular, this covers étale kernels
without requiring a separate computation of the scheme-theoretic center.

For a coordinate morphism `f : H ⟶ K`, the source group is `Spec K`, so the connectedness
and reducedness assumptions are on `K`. In characteristic zero, Cartier's theorem makes
both the source and its kernel geometrically reduced, so every such connected isogeny is central.
No smoothness assumption is made on the target.

## References

* J. S. Milne, *Algebraic Groups* (2017), Remark 12.39(a) and Chapter 3 (Cartier's theorem).
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u

section GeometricallyReducedKernel

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k K] [Algebra.IsGeometricallyReduced k K] {f : H ⟶ K}

/-- An isogeny from a geometrically reduced and geometrically connected finite-type affine
group with geometrically reduced kernel is central. The assumptions on the source group are on
`K` because
coordinate arrows reverse group-scheme arrows. -/
theorem IsIsogeny.isCentralIsogeny_of_isGeometricallyReduced_kernel (hf : IsIsogeny f)
    (hK : geometricallyConnectedCommHopfAlgProperty k K)
    [Algebra.IsGeometricallyReduced k (K ⧸ (kernelHopfIdeal f).toIdeal)] :
    IsCentralIsogeny f := by
  let _ := moduleFinite_quotient_kernelHopfIdeal hf.finite
  apply (isCentralIsogeny_iff f).mpr
  exact ⟨hf.finite, hf.faithfullyFlat,
    (isNormal_kernelHopfIdeal f).isCentral_of_finite_of_isGeometricallyReduced
      (H := FiniteTypeCommHopfAlgCat.of k K) hK⟩

end GeometricallyReducedKernel

section CharZero

variable {k : Type u} [Field k] [CharZero k] {H K : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k K] {f : H ⟶ K}

/-- In characteristic zero, every isogeny from a geometrically connected finite-type affine
group is central. Cartier's theorem also applies to its finite kernel, so infinitesimal
kernels cannot occur. -/
theorem IsIsogeny.isCentralIsogeny_of_charZero (hf : IsIsogeny f)
    (hK : geometricallyConnectedCommHopfAlgProperty k K) : IsCentralIsogeny f := by
  let _ : Algebra.Smooth k K :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k K)
  let _ : Algebra.IsGeometricallyReduced k K := isGeometricallyReduced_of_smooth k K
  let Q := quotient K (kernelHopfIdeal f)
  let _ : Module.Finite k Q := moduleFinite_quotient_kernelHopfIdeal hf.finite
  let _ : Algebra.Smooth k Q :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k Q)
  let _ : Algebra.IsGeometricallyReduced k Q := isGeometricallyReduced_of_smooth k Q
  exact hf.isCentralIsogeny_of_isGeometricallyReduced_kernel hK

end CharZero

end TauCeti.CommHopfAlgCat
