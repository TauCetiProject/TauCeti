/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Krasner
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PrimitiveElement

/-!
# The algebraic closure of a dense subfield inside the algebraic closure of a completion

Let `L` be a complete nontrivially normed nonarchimedean field, `K` a field whose image in `L` is
dense, and `Ω` a field over `L`. Every element of `Ω` separable over `L` generates the same
extension of `L` as some element of `Ω` algebraic over `K`: in an algebraic closure of `L`, with
its spectral norm, approximate the minimal polynomial over `L` by a monic polynomial over `K` of
the same degree, take a root of the latter close to the element (continuity of roots), and apply
Krasner's lemma, Mathlib's `IsKrasner.krasner`.

Hence, when `Ω / L` is algebraic and separable (for instance an algebraic closure of `L` in
characteristic zero) and `ι : Kbar →ₐ[K] Ω` embeds an algebraically closed field over `K`, the
field `Ω` is the compositum `L · ι(Kbar)`, an `L`-algebra map out of `Ω` is determined by its
values on `ι(Kbar)`, and every finite separable extension of `L` inside `Ω` is `L⟮ι β⟯` for some
`β ∈ Kbar`. For a number field `F`, a finite place `v`, `L = F_v`, `Ω = F̄_v` and `Kbar = F̄`
this is the comparison of the global and local algebraic closures (ArithmeticGaloisRepresentations
§2.1): an `F_v`-automorphism of `F̄_v` fixing `ι(F̄)` is the identity.

## Main results

* `IsSeparable.exists_isAlgebraic_adjoin_simple_eq`: an element separable over `L` generates the
  same extension of `L` as an element algebraic over `K`.
* `IntermediateField.adjoin_range_eq_top_of_denseRange`: `Ω` is generated over `L` by `ι(Kbar)`.
* `AlgHom.ext_of_denseRange`: `L`-algebra maps out of `Ω` agreeing on `ι(Kbar)` are equal.
* `IntermediateField.exists_eq_adjoin_simple_of_denseRange`: every finite extension of `L`
  inside `Ω` is `L⟮ι β⟯`.

## References

* H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, Current Developments in
  Mathematics 1995, §2.1, p. 51, for the case `K = ℚ`, `L = ℚ_p`.
* B. Conrad, *Algebraic closure of a complete field*, Math 248A handout, for the approximation
  argument.
-/

public section

open IntermediateField Polynomial

variable {K L Ω : Type*} [Field K] [NontriviallyNormedField L] [CompleteSpace L]
  [IsUltrametricDist L] [Algebra K L] [Field Ω] [Algebra L Ω] [Algebra K Ω]
  [IsScalarTower K L Ω]

/-- `IsSeparable.exists_isAlgebraic_adjoin_simple_eq` in an algebraic closure of `L`, which
carries the spectral norm. -/
private theorem exists_isAlgebraic_adjoin_simple_eq_of_isAlgClosed [IsAlgClosed Ω]
    [Algebra.IsAlgebraic L Ω] (hK : DenseRange (algebraMap K L)) {x : Ω} (hx : IsSeparable L x) :
    ∃ y : Ω, IsAlgebraic K y ∧ L⟮x⟯ = L⟮y⟯ := by
  let := spectralNorm.nontriviallyNormedField L Ω
  let := spectralNorm.normedAlgebra L Ω
  have : IsUltrametricDist Ω := IsUltrametricDist.of_normedAlgebra L
  have hxi : IsIntegral L x := hx.isIntegral
  -- `δ` separates `x` from its other conjugates: the conjugates form a finite, closed set
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp <|
    (((minpoly L x).rootSet_finite Ω).sdiff (t := {x})).isClosed.isOpen_compl.mem_nhds
      (by simp : x ∉ (minpoly L x).rootSet Ω \ {x})
  have hfm : (minpoly L x).Monic := minpoly.monic hxi
  have hn : (minpoly L x).natDegree ≠ 0 := (minpoly.natDegree_pos hxi).ne'
  have hM : 0 < max ‖x‖ 1 := lt_max_of_lt_right one_pos
  -- the coefficient precision that continuity of roots turns into the distance `δ`
  have hε : 0 < (δ / max ‖x‖ 1) ^ (minpoly L x).natDegree / ((minpoly L x).natDegree + 1) := by
    positivity
  obtain ⟨g, hgm, hdeg, hcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hK hfm hε
  obtain ⟨y, hy, hxy⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt hε (minpoly.aeval L x)
    hfm (hgm.map _) (by rw [natDegree_map, hdeg]) hcoeff (IsAlgClosed.splits _)
  rw [mul_div_cancel₀ _ (by positivity), Real.pow_rpow_inv_natCast (div_pos hδ hM).le hn,
    div_mul_cancel₀ _ hM.ne'] at hxy
  have hgy : aeval y (g.map (algebraMap K L)) = 0 := (mem_aroots.mp hy).2
  have hyi : IsIntegral L y := ⟨_, hgm.map _, by rwa [← aeval_def]⟩
  refine ⟨y, ⟨g, hgm.ne_zero, by rwa [aeval_map_algebraMap] at hgy⟩, ?_⟩
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
  refine eq_of_le_of_finrank_le hle ?_
  rw [adjoin.finrank hxi, adjoin.finrank hyi, hdeg, ← natDegree_map (algebraMap K L)]
  exact natDegree_le_natDegree (minpoly.degree_le_of_ne_zero L y (hgm.map _).ne_zero hgy)

/-- An element of a field `Ω` over a complete nonarchimedean field `L`, separable over `L`,
generates the same extension of `L` as an element of `Ω` algebraic over a dense subfield `K` of
`L` (Krasner's lemma). -/
theorem IsSeparable.exists_isAlgebraic_adjoin_simple_eq (hK : DenseRange (algebraMap K L))
    {x : Ω} (hx : IsSeparable L x) : ∃ y : Ω, IsAlgebraic K y ∧ L⟮x⟯ = L⟮y⟯ := by
  -- embed `L⟮x⟯` into an algebraic closure of `L` and work there
  have : FiniteDimensional L L⟮x⟯ := adjoin.finiteDimensional hx.isIntegral
  let ψ : L⟮x⟯ →ₐ[L] AlgebraicClosure L := IsAlgClosed.lift
  set x₀ := AdjoinSimple.gen L x
  have htop : L⟮x₀⟯ = ⊤ := lift_injective _ (by rw [lift_adjoin_simple, lift_top]; rfl)
  have hsep : IsSeparable L (ψ x₀) := by
    rwa [IsSeparable, minpoly.algHom_eq ψ ψ.injective, minpoly_gen]
  obtain ⟨y', hy', hxy'⟩ := exists_isAlgebraic_adjoin_simple_eq_of_isAlgClosed hK hsep
  have hmap (w : L⟮x⟯) : L⟮ψ w⟯ = L⟮w⟯.map ψ := by
    rw [adjoin_map, Set.image_singleton]
  obtain ⟨z, rfl⟩ : ∃ z, ψ z = y' := AlgHom.mem_fieldRange.mp <| by
    rw [AlgHom.fieldRange_eq_map, ← htop, ← hmap, hxy']
    exact mem_adjoin_simple_self L y'
  refine ⟨z, (isAlgebraic_algHom_iff (ψ.restrictScalars K) ψ.injective).mp hy' |>.algHom
    ((L⟮x⟯).val.restrictScalars K), ?_⟩
  have hz : L⟮z⟯ = ⊤ := map_injective ψ (by rw [← hmap, ← hxy', hmap, htop])
  rw [← lift_adjoin_simple, hz, lift_top]

/-- A separable algebraic extension `Ω` of a complete nonarchimedean field `L` is generated over
`L` by the elements algebraic over a dense subfield `K` of `L`. -/
theorem IntermediateField.adjoin_algebraicClosure_eq_top_of_denseRange
    [Algebra.IsSeparable L Ω] (hK : DenseRange (algebraMap K L)) :
    adjoin L ((algebraicClosure K Ω : IntermediateField K Ω) : Set Ω) = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨y, hy, hxy⟩ :=
    (Algebra.IsSeparable.isSeparable L x).exists_isAlgebraic_adjoin_simple_eq hK
  exact adjoin_simple_le_iff.mp (hxy.trans_le (adjoin_simple_le_iff.mpr
    (subset_adjoin L _ (mem_algebraicClosure_iff.mpr hy))))

variable {Kbar : Type*} [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]

omit [Algebra L Ω] [IsScalarTower K L Ω] in
/-- An element of `Ω` algebraic over `K` lies in the image of an algebraically closed field over
`K`. -/
private theorem algebraicClosure_subset_range (ι : Kbar →ₐ[K] Ω) :
    (algebraicClosure K Ω : Set Ω) ⊆ Set.range ι := fun y hy ↦ by
  have hyi := (mem_algebraicClosure_iff.mp hy).isIntegral
  have hmem : y ∈ (minpoly K y).rootSet Ω :=
    mem_rootSet.mpr ⟨minpoly.ne_zero hyi, minpoly.aeval K y⟩
  obtain ⟨b, -, rfl⟩ := ((IsAlgClosed.splits _).image_rootSet ι).ge hmem
  exact ⟨b, rfl⟩

/-- **The global closure generates the local closure.** If `ι : Kbar →ₐ[K] Ω` embeds an
algebraically closed field over a dense subfield `K` of a complete nonarchimedean field `L` into a
separable algebraic extension `Ω` of `L`, then `Ω` is the compositum `L · ι(Kbar)`. -/
theorem IntermediateField.adjoin_range_eq_top_of_denseRange [Algebra.IsSeparable L Ω]
    (hK : DenseRange (algebraMap K L)) (ι : Kbar →ₐ[K] Ω) :
    adjoin L (Set.range ι) = ⊤ :=
  top_unique <| (adjoin_algebraicClosure_eq_top_of_denseRange hK).ge.trans
    (adjoin.mono L _ _ (algebraicClosure_subset_range ι))

/-- Two `L`-algebra maps out of a separable algebraic extension `Ω` of a complete nonarchimedean
field `L` that agree on the image of an algebraically closed field over a dense subfield `K` of
`L` are equal. In particular an `L`-automorphism of `Ω` fixing `ι(Kbar)` is the identity. -/
theorem AlgHom.ext_of_denseRange [Algebra.IsSeparable L Ω] (hK : DenseRange (algebraMap K L))
    (ι : Kbar →ₐ[K] Ω) {B : Type*} [Ring B] [Algebra L B]
    ⦃φ₁ φ₂ : Ω →ₐ[L] B⦄ (h : ∀ b, φ₁ (ι b) = φ₂ (ι b)) : φ₁ = φ₂ := by
  have halg : ∀ x ∈ Set.range ι, IsAlgebraic L x := fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x
  refine AlgHom.ext_of_adjoin_eq_top (s := Set.range ι) ?_ (by rintro _ ⟨b, rfl⟩; exact h b)
  rw [← adjoin_toSubalgebra_of_isAlgebraic halg, adjoin_range_eq_top_of_denseRange hK ι,
    top_toSubalgebra]

/-- Every finite separable extension of a complete nonarchimedean field `L` inside a field `Ω` is
generated by the image of one element of an algebraically closed field over a dense subfield `K`
of `L`. -/
theorem IntermediateField.exists_eq_adjoin_simple_of_denseRange
    (hK : DenseRange (algebraMap K L)) (ι : Kbar →ₐ[K] Ω) (E : IntermediateField L Ω)
    [FiniteDimensional L E] [Algebra.IsSeparable L E] : ∃ b : Kbar, E = L⟮ι b⟯ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element L E
  have hE : E = L⟮(α : Ω)⟯ := by rw [← lift_adjoin_simple, hα, lift_top]
  have hsep : IsSeparable L (α : Ω) :=
    (Algebra.IsSeparable.isSeparable L α).map E.val E.val.injective
  obtain ⟨y, hy, hαy⟩ := hsep.exists_isAlgebraic_adjoin_simple_eq hK
  obtain ⟨b, rfl⟩ : y ∈ Set.range ι :=
    algebraicClosure_subset_range ι (mem_algebraicClosure_iff.mpr hy)
  exact ⟨b, hE.trans hαy⟩
