/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFreeQuotient
public import TauCeti.AlgebraicGeometry.StructureSheaf.StalkBaseAlgebra
public import TauCeti.RingTheory.TrivSqZeroExt
public import Mathlib.Algebra.DualNumber

/-!
# Check: the dual numbers in characteristic other than `2`

For a field `k` in which `2 ≠ 0` and `X = Spec k[ε]/(ε²)`, the sheaf `Ω_{X/k}` admits no locally
free quotient of rank `1`. The Kähler differentials of `k[ε]/(ε²)` are spanned by `dε`, and
`2ε dε = d(ε²) = 0`, so `ε` kills them; a surjection onto `k[ε]/(ε²)` would then force `ε = 0`.
By the stalk criterion it suffices to see this at the stalk of the closed point, which is
`k[ε]/(ε²)` itself, the ring being local (`StructureSheaf.toStalkAlgHom_closedPoint_bijective`).

In characteristic `2`, by contrast, `a + bε ↦ b` is a derivation and the predicate holds; so the
predicate depends on the characteristic even for a zero-dimensional scheme.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry KaehlerDifferential

namespace TauCeti.LocallyFreeQuotientDualNumberExample

universe u

variable {k : Type u} [Field k]

/-- If `ψ : k[ε]/(ε²) → S` is a surjective `k`-algebra map and `2 ≠ 0` in `k`, then `ψ ε` kills
the Kähler differentials `Ω[S⁄k]`: they are spanned by `d(ψ ε)`, and `2 ψ(ε) d(ψ ε) = d(ψ ε²)`
vanishes. -/
theorem smul_eq_zero_of_surjective {S : Type*} [CommRing S] [Algebra k S] (h2 : (2 : k) ≠ 0)
    (ψ : DualNumber k →ₐ[k] S) (hψ : Function.Surjective ψ) (ω : Ω[S⁄k]) :
    ψ DualNumber.eps • ω = 0 := by
  set e := ψ DualNumber.eps
  -- `e • d e = 0`: twice it is `d (e²) = 0`, and `2` is invertible.
  have hee : e • D k S e = 0 := by
    have h : (2 : k) • (e • D k S e) = 0 := by
      rw [two_smul, ← Derivation.leibniz, ← map_mul, DualNumber.eps_mul_eps, map_zero,
        Derivation.map_zero]
    simpa [h2] using h
  -- Every `d s` is a multiple of `d e`.
  have hspan : ∀ s : S, D k S s ∈ Submodule.span S {D k S e} := fun s ↦ by
    obtain ⟨a, rfl⟩ := hψ s
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq a, DualNumber.inr_eq_smul_eps,
      ← TrivSqZeroExt.algebraMap_eq_inl]
    simpa using Submodule.smul_of_tower_mem _ a.snd (Submodule.mem_span_singleton_self _)
  have hω : ω ∈ Submodule.span S {D k S e} := by
    have := span_range_derivation k S ▸ Submodule.mem_top (x := ω)
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hspan) this
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hω
  rw [smul_comm, hee, smul_zero]

/-- If `ψ : k[ε]/(ε²) → S` is a surjective `k`-algebra map with `ψ ε ≠ 0` and `2 ≠ 0` in `k`, then
there is no surjective `S`-linear map `Ω[S⁄k] → S^d` with `d ≠ 0`. -/
theorem not_surjective (h2 : (2 : k) ≠ 0) {S : Type*} [CommRing S] [Algebra k S]
    (ψ : DualNumber k →ₐ[k] S) (hψ : Function.Surjective ψ) (hε : ψ DualNumber.eps ≠ 0)
    {d : ℕ} (hd : d ≠ 0) (g : Ω[S⁄k] →ₗ[S] (Fin d → S)) : ¬ Function.Surjective g := by
  intro hg
  obtain ⟨ω, hω⟩ := hg fun _ ↦ 1
  have := congrFun (congrArg g (smul_eq_zero_of_surjective h2 ψ hψ ω)) ⟨0, Nat.pos_of_ne_zero hd⟩
  rw [map_smul, hω, map_zero] at this
  exact hε (by simpa using this)

variable (k) in
/-- The dual numbers `k[ε]/(ε²)`, as a commutative ring. -/
abbrev dualNumberRing : CommRingCat.{u} := .of (DualNumber k)

variable (k) in
/-- The closed point of `Spec k[ε]/(ε²)`, its only point. -/
abbrev closedPt : Spec (dualNumberRing k) := IsLocalRing.closedPoint (dualNumberRing k)

/-- **Check.** For a field `k` with `2 ≠ 0`, `Ω_{X/k}` for `X = Spec k[ε]/(ε²)` admits no locally
free quotient of rank `1`. -/
theorem not_hasLocallyFreeQuotientOfDifferentials_one (h2 : (2 : k) ≠ 0) :
    ¬ HasLocallyFreeQuotientOfDifferentials k (Spec (dualNumberRing k)) 1 := fun h ↦ by
  obtain ⟨g, hg⟩ := h.exists_surjective_stalk (closedPt k)
  -- Stated at `closedPt k`, typed as a point of `Spec`, so that the stalk's `k`-algebra
  -- instance `Scheme.stalkBaseAlgebra` is found.
  have hbij : Function.Bijective (StructureSheaf.toStalkAlgHom k _ (closedPt k)) :=
    StructureSheaf.toStalkAlgHom_closedPoint_bijective k _
  refine not_surjective h2 _ hbij.2 ?_ one_ne_zero g hg
  rw [Ne, ← map_zero (StructureSheaf.toStalkAlgHom k _ _), hbij.1.eq_iff]
  intro h
  simpa using congrArg TrivSqZeroExt.snd h

end TauCeti.LocallyFreeQuotientDualNumberExample
