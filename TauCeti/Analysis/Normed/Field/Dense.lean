/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.Topology.MetricSpace.Ultra.Basic

import Mathlib.Analysis.Normed.Field.Krasner
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.PurelyInseparable.Basic
import TauCeti.Analysis.Normed.Field.Approximation
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.FieldTheory.IsSepClosed

/-!
# The separable closure of a dense subfield inside the separable closure of a completion

Let `L` be a complete nonarchimedean normed field, `K` a field whose image in `L` is dense, and
`Ω` a field over `L`. Every element of `Ω` separable over `L` generates the same extension of `L`
as some element of `Ω` separable over `K`. Consequently the separable closure of `L` in `Ω` is
generated over `L` by the separable closure of `K` in `Ω`, and every finite separable extension
of `L` inside `Ω` is `L⟮y⟯` for an element `y` separable over `K`.

If moreover `ι : Kbar →ₐ[K] Ω` embeds a separably closed field over `K`, the separable closure of
`L` in `Ω` lies in the compositum `L · ι(Kbar)`, two `L`-algebra maps out of `Ω` that agree on
`ι(Kbar)` agree on the separable closure of `L` in `Ω`, and every finite separable extension of
`L` inside `Ω` is `L⟮ι β⟯` for some `β ∈ Kbar`. For a number field `F`, a finite place `v`,
`L = F_v`, `Ω = F_v^alg` and `Kbar = F^alg` this is the comparison of the global and local
algebraic closures: an `F_v`-automorphism of `F_v^alg` fixing `ι(F^alg)` is the identity, so
restriction along `ι` from the absolute Galois group of `F_v` to that of `F` is injective. This is
the key step towards identifying the former with a decomposition group of `F`, which is not done
here.

## Main results

* `IsSeparable.exists_isSeparable_adjoin_simple_eq_of_denseRange`: an element separable over `L`
  generates the same extension of `L` as an element separable over `K`.
* `TauCeti.IntermediateField.adjoin_separableClosure_eq_of_denseRange`: the separable closure of
  `L` in `Ω` is generated over `L` by the separable closure of `K` in `Ω`; when `Ω / L` is
  separable, `Ω` is generated over `L` by the elements separable, or algebraic, over `K`
  (`adjoin_separableClosure_eq_top_of_denseRange`, `adjoin_algebraicClosure_eq_top_of_denseRange`).
* `IntermediateField.exists_isSeparable_eq_adjoin_simple_of_denseRange`: every finite
  separable extension of `L` inside `Ω` is `L⟮y⟯` with `y` separable over `K`.
* `TauCeti.IntermediateField.separableClosure_le_adjoin_range_of_denseRange`: the separable
  closure of `L` in `Ω` lies in `L · ι(Kbar)`; when `Ω / L` is separable, `Ω = L · ι(Kbar)`
  (`adjoin_range_eq_top_of_denseRange`).
* `TauCeti.IntermediateField.eqOn_separableClosure_of_isSepClosed_of_denseRange`: `L`-algebra maps
  out of `Ω` agreeing on `ι(Kbar)` agree on the separable closure of `L` in `Ω`; they are equal
  when `Ω / L` is separable (`algHom_ext_of_isSepClosed_of_denseRange`), or algebraic with a
  reduced target (`algHom_ext_of_isAlgebraic_of_isSepClosed_of_denseRange`).
* `IntermediateField.exists_eq_adjoin_simple_of_denseRange`: every finite separable
  extension of `L` inside `Ω` is `L⟮ι β⟯`.

## Implementation notes

The first result is proved in an algebraic closure of `L` with its spectral norm, after embedding
`L⟮x⟯` there. The minimal polynomial of `x` over `L` is approximated by a monic polynomial `g` over
`K` of the same degree with a root `y` close to `x`
(`IsAlgebraic.exists_monic_and_natDegree_eq_and_aeval_eq_zero_and_norm_sub_lt`), Krasner's lemma
(`IsKrasner.krasner`) gives `L⟮x⟯ ≤ L⟮y⟯`, and comparing degrees gives equality. Then
`g.map (algebraMap K L)` is the minimal polynomial of `y` over `L`, which is separable, so `g` and
hence `y` are separable over `K`. A trivially normed `L` is discrete, so `K` maps onto `L` and
`y = x` works.

## References

* H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, Current Developments in
  Mathematics 1995, §2.1, for the case `K = ℚ`, `L = ℚ_p`.
* B. Conrad, *Completion of algebraic closure*, Math 248A handout, Corollary 3.3, for the
  approximation of separable polynomials.
-/

public section

open IntermediateField Polynomial

/-- `IsSeparable.exists_isSeparable_adjoin_simple_eq_of_denseRange` in an algebraic closure of a
nontrivially normed `L`, which carries the spectral norm. -/
private theorem exists_isSeparable_adjoin_simple_eq_of_isAlgClosed {K L Ω : Type*} [Field K]
    [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] [Algebra K L] [Field Ω]
    [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic L Ω]
    (hK : DenseRange (algebraMap K L)) {x : Ω} (hx : IsSeparable L x) :
    ∃ y : Ω, IsSeparable K y ∧ L⟮x⟯ = L⟮y⟯ := by
  let := spectralNorm.nontriviallyNormedField L Ω
  let := spectralNorm.normedAlgebra L Ω
  have : IsUltrametricDist Ω := IsUltrametricDist.of_normedAlgebra L
  have hxi : IsIntegral L x := hx.isIntegral
  -- `δ` separates `x` from its other conjugates: the conjugates form a finite, closed set
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp <|
    (((minpoly L x).rootSet_finite Ω).sdiff (t := {x})).isClosed.isOpen_compl.mem_nhds
      (by simp : x ∉ (minpoly L x).rootSet Ω \ {x})
  obtain ⟨g, y, hgm, hdeg, hgy, hxy⟩ :=
    hxi.isAlgebraic.exists_monic_and_natDegree_eq_and_aeval_eq_zero_and_norm_sub_lt hK hδ
  have hgyL : aeval y (g.map (algebraMap K L)) = 0 := by rwa [aeval_map_algebraMap]
  have hyi : IsIntegral L y := ⟨_, hgm.map _, by rwa [← aeval_def]⟩
  -- Krasner's lemma puts `x` in `L⟮y⟯`
  have hle : L⟮x⟯ ≤ L⟮y⟯ := by
    refine adjoin_simple_le_iff.mpr (IsKrasner.krasner hx (IsAlgClosed.splits _) hyi
      fun x' hx' hne ↦ ?_)
    have hmem : x' ∈ (minpoly L x).rootSet Ω \ {x} :=
      ⟨(isConjRoot_iff_mem_minpoly_rootSet hxi).mp hx', Ne.symm hne⟩
    have hδx' : δ ≤ dist x' x := by
      by_contra! h
      exact hball (Metric.mem_ball.mpr h) hmem
    exact hxy.trans_le (by rwa [dist_comm, dist_eq_norm] at hδx')
  -- `y` is a root of a polynomial of the degree of `x`, so the inclusion is an equality
  have : FiniteDimensional L L⟮y⟯ := adjoin.finiteDimensional hyi
  have hxy' : L⟮x⟯ = L⟮y⟯ := by
    refine eq_of_le_of_finrank_le hle ?_
    rw [adjoin.finrank hxi, adjoin.finrank hyi, hdeg, ← natDegree_map (algebraMap K L)]
    exact natDegree_le_natDegree (minpoly.degree_le_of_ne_zero L y (hgm.map _).ne_zero hgyL)
  refine ⟨y, ?_, hxy'⟩
  -- `g.map (algebraMap K L)` is the minimal polynomial of `y` over `L`, separable as `y ∈ L⟮x⟯`
  have hyL : IsSeparable L y := by
    have : Algebra.IsSeparable L L⟮y⟯ := by
      rw [← hxy']
      exact (isSeparable_adjoin_simple_iff_isSeparable L Ω).mpr hx
    exact (isSeparable_adjoin_simple_iff_isSeparable L Ω).mp this
  have hmin : g.map (algebraMap K L) = minpoly L y := by
    refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hyi) (hgm.map _)
      (minpoly.dvd L y hgyL) ?_
    rw [natDegree_map, ← hdeg, ← adjoin.finrank hxi, hxy', adjoin.finrank hyi]
  rw [IsSeparable, ← hmin, separable_map] at hyL
  exact hyL.of_dvd (minpoly.dvd K y hgy)

variable {K L Ω : Type*} [Field K] [NormedField L] [CompleteSpace L] [IsUltrametricDist L]
  [Algebra K L] [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

/-- An element of a field `Ω` over a complete nonarchimedean field `L`, separable over `L`,
generates the same extension of `L` as an element of `Ω` separable over a dense subfield `K` of
`L`. -/
theorem IsSeparable.exists_isSeparable_adjoin_simple_eq_of_denseRange {x : Ω}
    (hx : IsSeparable L x) (hK : DenseRange (algebraMap K L)) :
    ∃ y : Ω, IsSeparable K y ∧ L⟮x⟯ = L⟮y⟯ := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField L with hd | ⟨_, rfl⟩
  · -- a discrete `L` is the image of the dense subfield `K`, so `x` itself works
    have hsurj : Function.Surjective (algebraMap K L) := Set.range_eq_univ.mp <| by
      rw [← hK.closure_range, (isClosed_discrete _).closure_eq]
    obtain ⟨g, hg⟩ := map_surjective (algebraMap K L) hsurj (minpoly L x)
    have hgx : aeval x g = 0 := by rw [← aeval_map_algebraMap L, hg, minpoly.aeval]
    exact ⟨x, ((separable_map _).mp (hg ▸ hx : (g.map (algebraMap K L)).Separable)).of_dvd
      (minpoly.dvd K x hgx), rfl⟩
  -- embed `L⟮x⟯` into an algebraic closure of `L` and work there
  have : FiniteDimensional L L⟮x⟯ := adjoin.finiteDimensional hx.isIntegral
  let ψ : L⟮x⟯ →ₐ[L] AlgebraicClosure L := IsAlgClosed.lift
  set x₀ := AdjoinSimple.gen L x
  have htop : L⟮x₀⟯ = ⊤ := adjoin_adjoinSimple_gen_eq_top x
  have hsep : IsSeparable L (ψ x₀) := by
    rwa [IsSeparable, minpoly.algHom_eq ψ ψ.injective, minpoly_gen]
  obtain ⟨y', hy', hxy'⟩ := exists_isSeparable_adjoin_simple_eq_of_isAlgClosed hK hsep
  have hmap (w : L⟮x⟯) : L⟮ψ w⟯ = L⟮w⟯.map ψ := by
    rw [adjoin_map, Set.image_singleton]
  obtain ⟨z, rfl⟩ : ∃ z, ψ z = y' := AlgHom.mem_fieldRange.mp <| by
    rw [AlgHom.fieldRange_eq_map, ← htop, ← hmap, hxy']
    exact mem_adjoin_simple_self L y'
  refine ⟨z, (IsSeparable.of_algHom (f := ψ.restrictScalars K) (h := hy')).map
    ((L⟮x⟯).val.restrictScalars K) (L⟮x⟯).val.injective, ?_⟩
  have hz : L⟮z⟯ = ⊤ := map_injective ψ (by rw [← hmap, ← hxy', hmap, htop])
  rw [← lift_adjoin_simple, hz, lift_top]

namespace TauCeti.IntermediateField

/-- The separable closure of a complete nonarchimedean field `L` in a field `Ω` is generated over
`L` by the elements of `Ω` separable over a dense subfield `K` of `L`. -/
theorem adjoin_separableClosure_eq_of_denseRange (hK : DenseRange (algebraMap K L)) :
    adjoin L ((separableClosure K Ω : IntermediateField K Ω) : Set Ω) = separableClosure L Ω := by
  refine le_antisymm (separableClosure.adjoin_le K L Ω) fun x hx ↦ ?_
  obtain ⟨y, hy, hxy⟩ :=
    (mem_separableClosure_iff.mp hx).exists_isSeparable_adjoin_simple_eq_of_denseRange hK
  exact adjoin_simple_le_iff.mp (hxy.trans_le (adjoin_simple_le_iff.mpr
    (subset_adjoin L _ (mem_separableClosure_iff.mpr hy))))

/-- A separable extension `Ω` of a complete nonarchimedean field `L` is generated over `L` by the
elements separable over a dense subfield `K` of `L`. -/
theorem adjoin_separableClosure_eq_top_of_denseRange [Algebra.IsSeparable L Ω]
    (hK : DenseRange (algebraMap K L)) :
    adjoin L ((separableClosure K Ω : IntermediateField K Ω) : Set Ω) = ⊤ := by
  rw [adjoin_separableClosure_eq_of_denseRange hK, _root_.separableClosure.eq_top_iff]
  infer_instance

/-- A separable extension `Ω` of a complete nonarchimedean field `L` is generated over `L` by the
elements algebraic over a dense subfield `K` of `L`. -/
theorem adjoin_algebraicClosure_eq_top_of_denseRange [Algebra.IsSeparable L Ω]
    (hK : DenseRange (algebraMap K L)) :
    adjoin L ((algebraicClosure K Ω : IntermediateField K Ω) : Set Ω) = ⊤ :=
  top_unique <| (adjoin_separableClosure_eq_top_of_denseRange hK).ge.trans
    (adjoin.mono L _ _ fun _ hy ↦
      mem_algebraicClosure_iff.mpr (mem_separableClosure_iff.mp hy).isIntegral.isAlgebraic)

/-- Every finite separable extension of a complete nonarchimedean field `L` inside a field `Ω` is
generated by one element of `Ω` separable over a dense subfield `K` of `L`. -/
theorem _root_.IntermediateField.exists_isSeparable_eq_adjoin_simple_of_denseRange
    (hK : DenseRange (algebraMap K L))
    (E : IntermediateField L Ω) [FiniteDimensional L E] [Algebra.IsSeparable L E] :
    ∃ y : Ω, IsSeparable K y ∧ E = L⟮y⟯ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element L E
  have hE : E = L⟮(α : Ω)⟯ := by rw [← lift_adjoin_simple, hα, lift_top]
  obtain ⟨y, hy, hαy⟩ := ((Algebra.IsSeparable.isSeparable L α).map E.val
    E.val.injective).exists_isSeparable_adjoin_simple_eq_of_denseRange hK
  exact ⟨y, hy, hE.trans hαy⟩

variable {Kbar : Type*} [Field Kbar] [Algebra K Kbar] [IsSepClosed Kbar]

/-- **The global closure generates the local closure.** If `ι : Kbar →ₐ[K] Ω` embeds a separably
closed field over a dense subfield `K` of a complete nonarchimedean field `L` into a field `Ω` over
`L`, then the separable closure of `L` in `Ω` lies in the compositum `L · ι(Kbar)`. -/
theorem separableClosure_le_adjoin_range_of_denseRange (hK : DenseRange (algebraMap K L))
    (ι : Kbar →ₐ[K] Ω) : separableClosure L Ω ≤ adjoin L (Set.range ι) :=
  (adjoin_separableClosure_eq_of_denseRange hK).ge.trans <| adjoin.mono L _ _ fun _ hy ↦
    AlgHom.mem_fieldRange.mp (ι.separableClosure_le_fieldRange hy)

/-- **The global closure generates the local closure.** If `ι : Kbar →ₐ[K] Ω` embeds a separably
closed field over a dense subfield `K` of a complete nonarchimedean field `L` into a separable
extension `Ω` of `L`, then `Ω` is the compositum `L · ι(Kbar)`. -/
theorem adjoin_range_eq_top_of_denseRange [Algebra.IsSeparable L Ω]
    (hK : DenseRange (algebraMap K L)) (ι : Kbar →ₐ[K] Ω) : adjoin L (Set.range ι) = ⊤ :=
  top_unique <| ((_root_.separableClosure.eq_top_iff L Ω).mpr inferInstance).ge.trans
    (separableClosure_le_adjoin_range_of_denseRange hK ι)

/-- Two `L`-algebra maps out of a field `Ω` over a complete nonarchimedean field `L` that agree on
the image of a separably closed field over a dense subfield `K` of `L` agree on the separable
closure of `L` in `Ω`. -/
theorem eqOn_separableClosure_of_isSepClosed_of_denseRange (hK : DenseRange (algebraMap K L))
    (ι : Kbar →ₐ[K] Ω) {B : Type*} [Semiring B] [Algebra L B] ⦃φ₁ φ₂ : Ω →ₐ[L] B⦄
    (h : ∀ b, φ₁ (ι b) = φ₂ (ι b)) : Set.EqOn φ₁ φ₂ (separableClosure L Ω) := by
  have halg : ∀ x ∈ ((separableClosure K Ω : IntermediateField K Ω) : Set Ω), IsAlgebraic L x :=
    fun x hx ↦ (mem_separableClosure_iff.mp hx).isIntegral.isAlgebraic.tower_top L
  rw [← adjoin_separableClosure_eq_of_denseRange hK, ← coe_toSubalgebra,
    adjoin_toSubalgebra_of_isAlgebraic halg, AlgHom.eqOn_adjoin_iff]
  intro y hy
  obtain ⟨b, rfl⟩ := AlgHom.mem_fieldRange.mp (ι.separableClosure_le_fieldRange hy)
  exact h b

/-- Two `L`-algebra maps out of a separable extension `Ω` of a complete nonarchimedean field `L`
that agree on the image of a separably closed field over a dense subfield `K` of `L` are equal.
In particular an `L`-automorphism of `Ω` fixing `ι(Kbar)` is the identity. -/
theorem algHom_ext_of_isSepClosed_of_denseRange [Algebra.IsSeparable L Ω]
    (hK : DenseRange (algebraMap K L)) (ι : Kbar →ₐ[K] Ω) {B : Type*} [Semiring B] [Algebra L B]
    ⦃φ₁ φ₂ : Ω →ₐ[L] B⦄ (h : ∀ b, φ₁ (ι b) = φ₂ (ι b)) : φ₁ = φ₂ :=
  algHom_ext_of_adjoin_eq_top (adjoin_range_eq_top_of_denseRange hK ι) (Set.forall_mem_range.mpr h)

/-- Two `L`-algebra maps into a reduced ring, out of an algebraic extension `Ω` of a complete
nonarchimedean field `L`, that agree on the image of a separably closed field over a dense
subfield `K` of `L` are equal: they agree on the separable closure of `L` in `Ω`, over which `Ω`
is purely inseparable. -/
theorem algHom_ext_of_isAlgebraic_of_isSepClosed_of_denseRange [Algebra.IsAlgebraic L Ω]
    (hK : DenseRange (algebraMap K L)) (ι : Kbar →ₐ[K] Ω) {B : Type*} [CommRing B] [IsReduced B]
    [Algebra L B] ⦃φ₁ φ₂ : Ω →ₐ[L] B⦄ (h : ∀ b, φ₁ (ι b) = φ₂ (ι b)) : φ₁ = φ₂ :=
  IsPurelyInseparable.injective_restrictDomain (separableClosure L Ω) Ω L B <| AlgHom.ext fun x ↦
    eqOn_separableClosure_of_isSepClosed_of_denseRange hK ι h x.property

/-- Every finite separable extension of a complete nonarchimedean field `L` inside a field `Ω` is
generated by the image of one element of a separably closed field over a dense subfield `K` of
`L`. -/
theorem _root_.IntermediateField.exists_eq_adjoin_simple_of_denseRange
    (hK : DenseRange (algebraMap K L)) (ι : Kbar →ₐ[K] Ω) (E : IntermediateField L Ω)
    [FiniteDimensional L E] [Algebra.IsSeparable L E] : ∃ b : Kbar, E = L⟮ι b⟯ := by
  obtain ⟨y, hy, hE⟩ := exists_isSeparable_eq_adjoin_simple_of_denseRange hK E
  obtain ⟨b, rfl⟩ :=
    AlgHom.mem_fieldRange.mp (ι.separableClosure_le_fieldRange (mem_separableClosure_iff.mpr hy))
  exact ⟨b, hE⟩

end TauCeti.IntermediateField
