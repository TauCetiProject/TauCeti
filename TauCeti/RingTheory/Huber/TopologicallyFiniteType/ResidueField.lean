/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Nullstellensatz

/-!
# Residue fields of algebras topologically of finite type over a field

Let `k` be a complete nonarchimedean field and `B` a topological `k`-algebra topologically of
finite type, that is `IsTopologicallyFiniteType (algebraMap k B)`. This file proves Wedhorn's
Proposition 5.61: for every maximal ideal `m` of `B` the residue field `B ⧸ m` is a finite extension
of `k`.

A presentation of `B` is a surjection from the completed Tate algebra `k⟨X₁, …, Xₙ⟩`, which is the
Gauss-normed algebra of restricted power series
(`TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussAlgEquiv`). So the statement is the
Nullstellensatz for quotients of Tate algebras,
`TauCeti.MvPowerSeries.finite_quotient_of_surjective`.

Over a finite extension of `k` the norm of `k` extends uniquely, so this is what attaches to a
maximal ideal of `B` a point of the adic spectrum `Spa(B, B°)` (Wedhorn, Example 7.58).

## Main results

* `TauCeti.Huber.IsTopologicallyFiniteType.exists_surjective_algHom`: a `k`-algebra topologically
  of finite type is a quotient of a Tate algebra `k⟨X₁, …, Xₙ⟩`.
* `TauCeti.Huber.IsTopologicallyFiniteType.finite_quotient_of_isMaximal`: the residue field of a
  maximal ideal of a `k`-algebra topologically of finite type is finite over `k`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.61 and
  Example 7.58.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.2,
  Corollary 3.
-/

public section

namespace TauCeti.Huber

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra K B]

/-- **A `K`-algebra topologically of finite type is a quotient of a Tate algebra**: there is a
surjective `K`-algebra map onto it from the Gauss-normed algebra `K⟨X₁, …, Xₙ⟩` of restricted
power series, for some `n`. -/
theorem IsTopologicallyFiniteType.exists_surjective_algHom
    (h : IsTopologicallyFiniteType (algebraMap K B)) :
    ∃ (n : ℕ) (φ : MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] B),
      Function.Surjective φ := by
  obtain ⟨n, π, hπ, hcomp⟩ :=
    isStrictlyTopologicallyFiniteType_iff.mp h.isStrictlyTopologicallyFiniteType
  let π' : restrictedMvPowerSeriesCompletion n K →ₐ[K] B :=
    { π with commutes' := fun r ↦ congrArg (· r) hcomp }
  exact ⟨n, π'.comp restrictedMvPowerSeriesCompletionGaussAlgEquiv.symm.toAlgHom,
    hπ.surjective.comp restrictedMvPowerSeriesCompletionGaussAlgEquiv.symm.surjective⟩

/-- **Wedhorn, Proposition 5.61.** Over a complete nonarchimedean field `K`, the residue field
`B ⧸ m` of every maximal ideal of a `K`-algebra `B` topologically of finite type is a finite
extension of `K`. -/
theorem IsTopologicallyFiniteType.finite_quotient_of_isMaximal
    (h : IsTopologicallyFiniteType (algebraMap K B)) (m : Ideal B) [m.IsMaximal] :
    Module.Finite K (B ⧸ m) := by
  obtain ⟨n, φ, hφ⟩ := h.exists_surjective_algHom
  exact MvPowerSeries.finite_quotient_of_surjective hφ m

end TauCeti.Huber
