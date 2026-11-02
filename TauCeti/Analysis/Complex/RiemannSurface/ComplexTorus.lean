/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.DiscreteSubgroupStabilizer
public import TauCeti.Geometry.Diffeomorphism.FixingSubgroup.Basic
public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Algebra.Module.ZLattice.Quotient
import TauCeti.Geometry.Diffeomorphism.RelativeCongr
import TauCeti.Topology.Covering.Quotient

/-!
# Holomorphic maps and automorphisms of one-dimensional complex tori

Let `L` and `L'` be lattices in `ℂ`, discrete additive subgroups given as `ℤ`-submodules, with
`L` of full rank. The complex tori `ℂ / L` and `ℂ / L'` are the orbit spaces
`AddAction.orbitRel.Quotient L ℂ` with their quotient complex structure. Every holomorphic map
`f : ℂ / L → ℂ / L'` is induced by an affine map: there are `a b : ℂ` with `a L ⊆ L'` and
`f [z] = [a z + b]` (`ContMDiff.exists_apply_mk_eq_mul_add`). Lift the composite of `f` with the
projection `ℂ → ℂ / L` through the covering `ℂ → ℂ / L'` to a holomorphic `F : ℂ → ℂ`; for
`l ∈ L` the difference `F (z + l) - F z` is a continuous function with values in the discrete set
`L'`, hence constant, so `F'` is `L`-periodic and bounded, and constant by Liouville's theorem.

For a biholomorphism of `ℂ / L` the factor `a` is a unit with `a L = L`, an element of the lattice
stabilizer `MulAction.stabilizer ℂˣ L` (`Diffeomorph.exists_apply_mk_eq_mul_add`). So every
automorphism of `ℂ / L` is a translation composed with a linear automorphism `[z] ↦ [u z]`, and
the stabilizer, which contains `-1`, is finite (`Submodule.finite_stabilizer_units`). An
automorphism fixing a point `[p]` is `[z] ↦ [u (z - p) + p]`, determined by `u`, so the
biholomorphisms fixing any nonempty set of points form a finite group, while the translations make
the full automorphism group infinite (`Diffeomorph.finite_fixingSubgroup_iff_nonempty`). For a
genus-one component of a marked nodal curve, this is the statement that the component is stable,
`2 g - 2 + n > 0`, exactly when its automorphisms fixing its special points form a finite group.

## Main results

* `ContMDiff.exists_apply_mk_eq_mul_add`: holomorphic maps of one-dimensional complex tori are
  induced by affine maps `z ↦ a z + b` with `a L ⊆ L'`.
* `Diffeomorph.exists_apply_mk_eq_mul_add`: biholomorphisms of `ℂ / L` are induced by affine maps
  `z ↦ u z + b` with `u` in the lattice stabilizer.
* `Diffeomorph.finite_fixingSubgroup_iff_nonempty`: on a manifold biholomorphic to `ℂ / L`, the
  biholomorphisms fixing a set `s` pointwise form a finite group exactly when `s` is nonempty.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Proposition 1.2.1, for
  holomorphic maps of complex tori as translates of homomorphisms induced by linear maps.
-/

public section

open Set
open scoped Manifold ContDiff Pointwise

variable {L L' : Submodule ℤ ℂ} [DiscreteTopology L] [DiscreteTopology L'] {n : ℕ∞ω}

/-- **Holomorphic maps of complex tori are affine.** A holomorphic map `f : ℂ / L → ℂ / L'`
between one-dimensional complex tori, with `L` a full lattice, is induced by an affine map
`z ↦ a * z + b` of `ℂ` with `a * l ∈ L'` for every `l ∈ L`. -/
theorem ContMDiff.exists_apply_mk_eq_mul_add [IsZLattice ℝ L]
    {f : AddAction.orbitRel.Quotient L ℂ → AddAction.orbitRel.Quotient L' ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n f) (hn : n ≠ 0) :
    ∃ a b : ℂ, (∀ l ∈ L, a * l ∈ L') ∧
      ∀ z, f (Quotient.mk _ z) = Quotient.mk (AddAction.orbitRel L' ℂ) (a * z + b) := by
  -- Lift `f` composed with the projection `ℂ → ℂ / L` through the covering map `ℂ → ℂ / L'`.
  obtain ⟨b, hb⟩ := Quotient.mk_surjective (f (Quotient.mk _ 0))
  obtain ⟨F, ⟨-, hF⟩, -⟩ :=
    (AddSubgroup.isAddQuotientCoveringMap_quotientMk L'.toAddSubgroup).isCoveringMap
      |>.existsUnique_continuousMap_lifts
        ⟨f ∘ Quotient.mk _, hf.continuous.comp continuous_quotient_mk'⟩ 0 b hb
  have hFπ (z : ℂ) :
      Quotient.mk (AddAction.orbitRel L' ℂ) (F z) = f (Quotient.mk _ z) := congrFun hF z
  -- The lift is holomorphic, since the projection `ℂ → ℂ / L'` is a local biholomorphism.
  have hπ' := TauCeti.isLocalDiffeomorph_addQuotientMk (G := L') (M := ℂ) (I := 𝓘(ℂ)) (n := n)
  have hFd : Differentiable ℂ F := by
    refine (contMDiff_iff_contDiff.mp ?_).differentiable hn
    refine ContMDiff.of_comp_isLocalDiffeomorph hπ' F.continuous ?_
    rw [show Quotient.mk (AddAction.orbitRel L' ℂ) ∘ F = f ∘ Quotient.mk _ from funext hFπ]
    exact hf.comp TauCeti.isLocalDiffeomorph_addQuotientMk.contMDiff
  -- Translating by a period of `L` changes the lift by a constant of `L'`.
  have hmem {z w : ℂ} (h : z - w ∈ L) : F z - F w ∈ L' := by
    rw [← L'.orbitRelQuotient_mk_eq_mk_iff, hFπ, hFπ, L.orbitRelQuotient_mk_eq_mk_iff.mpr h]
  have hper (l : ℂ) (hl : l ∈ L) (z : ℂ) : F (z + l) = F z + (F l - F 0) := by
    have := isPreconnected_univ.constant_of_mapsTo (isDiscrete_iff_discreteTopology.mpr ‹_›)
      (f := fun z ↦ F (z + l) - F z) (by fun_prop) (fun z _ ↦ hmem (by simpa using hl))
      (mem_univ z) (mem_univ 0)
    rw [zero_add] at this
    linear_combination this
  -- Hence `F'` is `L`-periodic, so bounded, and constant by Liouville's theorem.
  have hFd' : Differentiable ℂ (deriv F) := hFd.deriv
  have hderiv (z l : ℂ) (hl : l ∈ L) : deriv F (z + l) = deriv F z := by
    rw [← deriv_comp_add_const, funext (hper l hl), deriv_add_const]
  have hbdd : Bornology.IsBounded (range (deriv F)) :=
    (IsZLattice.isCompact_range_of_periodic L _ hFd'.continuous hderiv).isBounded
  have hFa (z : ℂ) : F z = deriv F 0 * z + F 0 := by
    have := is_const_of_deriv_eq_zero (f := fun z ↦ F z - deriv F 0 * z)
      (hFd.sub (differentiable_id.const_mul _)) (fun z ↦ ?_) z 0
    · simp only [mul_zero, sub_zero] at this
      linear_combination this
    · rw [((hFd z).hasDerivAt.fun_sub ((hasDerivAt_id' z).const_mul (deriv F 0))).deriv, mul_one,
        hFd'.apply_eq_apply_of_bounded hbdd z 0, sub_self]
  refine ⟨deriv F 0, F 0, fun l hl ↦ ?_, fun z ↦ by rw [← hFπ, hFa]⟩
  have := hmem (z := l) (w := 0) (by simpa using hl)
  rwa [hFa l, add_sub_cancel_right] at this

namespace Diffeomorph

/-- **Biholomorphisms of a complex torus.** Every biholomorphism of a one-dimensional complex torus
`ℂ / L` is induced by an affine map `z ↦ u * z + b` of `ℂ` whose linear part `u` is a unit
stabilizing the lattice, `u • L = L`. -/
theorem exists_apply_mk_eq_mul_add [IsZLattice ℝ L]
    (φ : AddAction.orbitRel.Quotient L ℂ ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ AddAction.orbitRel.Quotient L ℂ)
    (hn : n ≠ 0) :
    ∃ u ∈ MulAction.stabilizer ℂˣ L, ∃ b : ℂ,
      ∀ z, φ (Quotient.mk _ z) = Quotient.mk (AddAction.orbitRel L ℂ) (u * z + b) := by
  obtain ⟨a, b, ha, hφ⟩ := φ.contMDiff.exists_apply_mk_eq_mul_add hn
  obtain ⟨a', b', ha', hφ'⟩ := φ.symm.contMDiff.exists_apply_mk_eq_mul_add hn
  -- `φ⁻¹ ∘ φ = id` lifts to `z ↦ (a' * a - 1) * z + (a' * b + b')`, with values in `L`.
  have hmem (z : ℂ) : (a' * a - 1) * z + (a' * b + b') ∈ L := by
    have := φ.symm_apply_apply (Quotient.mk _ z)
    rw [hφ, hφ', L.orbitRelQuotient_mk_eq_mk_iff] at this
    convert this using 1
    ring
  have haa : a' * a = 1 := by
    linear_combination isPreconnected_univ.constant_of_mapsTo
      (isDiscrete_iff_discreteTopology.mpr ‹_›) (by fun_prop) (fun z _ ↦ hmem z) (mem_univ 1)
      (mem_univ 0)
  let u : ℂˣ := ⟨a, a', by linear_combination haa, haa⟩
  exact ⟨u, Submodule.mem_stabilizer_units_iff.mpr ⟨ha, ha'⟩, b, hφ⟩

/-- The biholomorphisms of a complex torus fixing a point are finite in number: such a map is
`[z] ↦ [u * (z - p) + p]`, determined by its linear part `u` in the finite lattice stabilizer. -/
private theorem finite_fixingSubgroup_of_nonempty [IsZLattice ℝ L] (hn : n ≠ 0)
    {s : Set (AddAction.orbitRel.Quotient L ℂ)} (hs : s.Nonempty) :
    Finite (fixingSubgroup (I := 𝓘(ℂ)) (n := n) s) := by
  obtain ⟨x, hx⟩ := hs
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective x
  have hL : L ≠ ⊥ := fun h ↦ by
    simpa [h] using (IsZLattice.span_top (K := ℝ) (L := L))
  have := L.finite_stabilizer_units hL
  choose u hu b hb using fun φ : fixingSubgroup (I := 𝓘(ℂ)) (n := n) s ↦
    (φ : AddAction.orbitRel.Quotient L ℂ ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ _).exists_apply_mk_eq_mul_add hn
  refine Finite.of_injective (fun φ ↦ (⟨u φ, hu φ⟩ : MulAction.stabilizer ℂˣ L)) fun φ ψ h ↦ ?_
  have hu : u φ = u ψ := congrArg Subtype.val h
  -- Both maps fix `[p]`, so their translation parts agree modulo `L`.
  have hbb : b φ - b ψ ∈ L := by
    have := L.orbitRelQuotient_mk_eq_mk_iff.mp
      (((hb φ p).symm.trans (apply_eq_of_mem_fixingSubgroup φ.2 hx)).trans
        ((hb ψ p).symm.trans (apply_eq_of_mem_fixingSubgroup ψ.2 hx)).symm)
    rw [hu] at this
    convert this using 1
    ring
  refine Subtype.ext (Diffeomorph.ext fun x ↦ Quotient.inductionOn x fun z ↦ ?_)
  rw [hb φ, hb ψ, hu, L.orbitRelQuotient_mk_eq_mk_iff]
  convert hbb using 1
  ring

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- **Automorphisms of a genus-one curve fixing points.** On a manifold biholomorphic to a
one-dimensional complex torus `ℂ / L`, the biholomorphisms fixing every point of a set `s` form
a finite group exactly when `s` is nonempty. With no point fixed, the translations of the torus
give infinitely many. -/
theorem finite_fixingSubgroup_iff_nonempty [IsZLattice ℝ L]
    (e : M ≃ₘ^n⟮I, 𝓘(ℂ)⟯ AddAction.orbitRel.Quotient L ℂ) (hn : n ≠ 0) {s : Set M} :
    Finite (fixingSubgroup (I := I) (n := n) s) ↔ s.Nonempty := by
  refine ⟨fun h ↦ nonempty_iff_ne_empty.mpr fun hs ↦ ?_, fun hs ↦ ?_⟩
  · rw [hs] at h
    exact not_finite_iff_infinite.mpr e.infinite_fixingSubgroup_empty h
  · have := finite_fixingSubgroup_of_nonempty (n := n) hn (hs.image e)
    exact Finite.of_equiv _ (relativeDiffCongr e s).symm.toEquiv

end Diffeomorph
