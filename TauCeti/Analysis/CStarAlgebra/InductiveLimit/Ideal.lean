/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleRing.Basic
public import TauCeti.Analysis.CStarAlgebra.InductiveLimit.Basic

/-!
# Closed two-sided ideals and simplicity of C⋆-inductive limits

Let `(A i, f i j)` be a directed system of (possibly nonunital) complex C⋆-algebras with
(not necessarily injective) `⋆`-homomorphisms as transition maps, and let
`L = CStarInductiveLimit A f`. Passing to the quotient C⋆-algebra `L ⧸ J` for any closed two-sided
ideal `J` of `L`, the factored `⋆`-homomorphism `A i ⧸ ker (mk_J ∘ of i) → L ⧸ J` is isometric by
`NonUnitalStarAlgHom.isometry_quotientKerHom`. Consequently, any element of `J` approximated within
`ε / 3` by `of i a` has `‖mk (ker (mk_J ∘ of i)) a‖ < ε / 3`, so subtracting a small representative
`b` of the same coset produces an element `a - b ∈ of i ⁻¹' J` whose image `of i (a - b)` is within
`ε` of the given element of `J`.

Thus every closed two-sided ideal `J` of `CStarInductiveLimit A f` equals the norm closure of
`⋃ i, of A f i '' (of A f i ⁻¹' J)` (Blackadar, *Operator Algebras*, II.8.2.3). In particular, if
cofinally many stages `A j` are C⋆-simple (have no closed two-sided ideals other than `⊥` and `⊤`),
then `CStarInductiveLimit A f` has no closed two-sided ideals other than `⊥` and `⊤`
(Blackadar, II.8.2.5), even when the transition maps fail to be injective.

## Main statements

* `TauCeti.CStarInductiveLimit.coe_ideal_eq_closure_iUnion` and
  `TauCeti.CStarInductiveLimit.ideal_eq_topologicalClosure_span`: every closed two-sided ideal `J`
  of `CStarInductiveLimit A f` is generated as a closed ideal by the images of its stage preimages.
* `TauCeti.CStarInductiveLimit.ideal_eq_bot_iff` and
  `TauCeti.CStarInductiveLimit.ideal_eq_top_iff`: characterizations of trivial and improper closed
  two-sided ideals via stage preimages.
* `TauCeti.CStarInductiveLimit.eq_bot_or_top_of_isClosed_cofinal`,
  `TauCeti.CStarInductiveLimit.eq_bot_or_top_of_isClosed`, and
  `TauCeti.CStarInductiveLimit.eq_bot_or_top_of_isClosed_of_isSimpleRing`: preservation of
  C⋆-simplicity under C⋆-inductive limits.

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Section II.8.2 (II.8.2.3, II.8.2.5).
* Kenneth R. Davidson, *C*-Algebras by Example*, Theorem III.4.2.
-/

public section

open scoped CStarAlgebra

namespace TauCeti.CStarInductiveLimit

universe u v

-- Verify across module boundaries that the unital and nonunital C⋆-algebra instances on
-- `CStarInductiveLimit` agree definitionally with zero instance diamonds.
example {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {A : ι → Type v} [∀ i, CStarAlgebra (A i)]
    {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ i j (h : i ≤ j), T h}
    [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
    [∀ i j h, AlgHomClass (T h) ℂ (A i) (A j)]
    [∀ i j h, StarHomClass (T h) (A i) (A j)] [DirectedSystem A (f · · ·)] :
    (instCStarAlgebra (A := A) (f := f)).toNonUnitalCStarAlgebra =
      instNonUnitalCStarAlgebra :=
  rfl

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {A : ι → Type v} [∀ i, NonUnitalCStarAlgebra (A i)]
  {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ i j (h : i ≤ j), T h}
  [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
  [∀ i j h, NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
  [∀ i j h, StarHomClass (T h) (A i) (A j)]
  [DirectedSystem A (f · · ·)]

/-- **Closed ideal structure of a C⋆-inductive limit** (Blackadar II.8.2.3): every closed
two-sided ideal `J` of `CStarInductiveLimit A f` is the norm closure of the union of the images of
its stage preimages `of A f i ⁻¹' J`, without assuming injective transition maps. -/
theorem coe_ideal_eq_closure_iUnion (J : TwoSidedIdeal (CStarInductiveLimit A f))
    [hJ : IsClosed (J : Set (CStarInductiveLimit A f))] :
    (J : Set (CStarInductiveLimit A f)) =
      closure (⋃ i, of A f i '' (of A f i ⁻¹' (J : Set (CStarInductiveLimit A f)))) := by
  refine Set.Subset.antisymm (fun x hx ↦ ?_) ?_
  · rw [Metric.mem_closure_iff]
    intro ε hε
    have hε3 : 0 < ε / 3 := by positivity
    -- Pass to the C⋆-quotient `L ⧸ J`, where the factored map from `A i ⧸ ker (mk_J ∘ of i)` is
    -- isometric by `NonUnitalStarAlgHom.isometry_quotientKerHom`.
    let π : CStarInductiveLimit A f →⋆ₙₐ[ℂ] CStarInductiveLimit A f ⧸ J :=
      TwoSidedIdeal.Quotient.mkStarAlgHom J
    obtain ⟨i, a, ha⟩ := exists_norm_sub_of_lt x hε3
    let ψ : A i →⋆ₙₐ[ℂ] CStarInductiveLimit A f ⧸ J := π.comp (of A f i)
    let K : TwoSidedIdeal (A i) := TwoSidedIdeal.ker ψ
    have hπx : π x = 0 := by
      dsimp only [π]
      rw [TwoSidedIdeal.Quotient.mkStarAlgHom_apply]
      exact TwoSidedIdeal.Quotient.eq_zero_iff_mem.mpr hx
    have hnorm_mk : ‖TwoSidedIdeal.Quotient.mk K a‖ < ε / 3 := by
      have hiso : ‖TwoSidedIdeal.Quotient.mk K a‖ = ‖ψ a‖ :=
        (ψ.isometry_quotientKerHom.norm_map_of_map_zero (map_zero _)
          (TwoSidedIdeal.Quotient.mk K a)).symm.trans (congrArg norm (ψ.quotientKerHom_mk a))
      rw [hiso]
      calc
        ‖ψ a‖ = ‖π (of A f i a - x)‖ := by
          simp only [ψ, NonUnitalStarAlgHom.comp_apply, map_sub, hπx, sub_zero]
        _ ≤ ‖of A f i a - x‖ := NonUnitalStarAlgHom.norm_apply_le π _
        _ = ‖x - of A f i a‖ := norm_sub_rev _ _
        _ < ε / 3 := ha
    obtain ⟨b, hb_mk, hb_norm⟩ :=
      TwoSidedIdeal.Quotient.exists_norm_mk_lt (TwoSidedIdeal.Quotient.mk K a) hε3
    have hc_ker : a - b ∈ K := by
      rw [← TwoSidedIdeal.Quotient.eq_zero_iff_mem, map_sub, hb_mk, sub_self]
    have hc_mem : of A f i (a - b) ∈ J := by
      have hψ0 : ψ (a - b) = 0 := (TwoSidedIdeal.mem_ker ψ).mp hc_ker
      dsimp only [ψ, π] at hψ0
      rw [NonUnitalStarAlgHom.comp_apply, TwoSidedIdeal.Quotient.mkStarAlgHom_apply] at hψ0
      exact TwoSidedIdeal.Quotient.eq_zero_iff_mem.mp hψ0
    refine ⟨of A f i (a - b), Set.mem_iUnion.mpr ⟨i, ⟨a - b, hc_mem, rfl⟩⟩, ?_⟩
    rw [dist_eq_norm]
    have hsplit : x - of A f i (a - b) = (x - of A f i a) + of A f i b := by
      rw [map_sub]
      abel
    calc
      ‖x - of A f i (a - b)‖ ≤ ‖x - of A f i a‖ + ‖of A f i b‖ :=
        hsplit ▸ norm_add_le _ _
      _ ≤ ‖x - of A f i a‖ + ‖b‖ := add_le_add_right (norm_of_le i b) _
      _ < ε / 3 + (ε / 3 + ε / 3) := add_lt_add ha (hb_norm.trans (add_lt_add_left hnorm_mk _))
      _ = ε := by ring
  · refine closure_minimal (Set.iUnion_subset fun i ↦ ?_) hJ
    rintro _ ⟨a, ha, rfl⟩
    exact ha

/-- Ideal-lattice form of `coe_ideal_eq_closure_iUnion`: every closed two-sided ideal `J` equals
the topological closure of the two-sided ideal generated by
`⋃ i, of A f i '' (J.comap (of A f i))`. -/
theorem ideal_eq_topologicalClosure_span (J : TwoSidedIdeal (CStarInductiveLimit A f))
    [hJ : IsClosed (J : Set (CStarInductiveLimit A f))] :
    J = (TwoSidedIdeal.span
      (⋃ i, of A f i '' (J.comap (of A f i) : Set (A i)))).topologicalClosure := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · rw [TwoSidedIdeal.mem_topologicalClosure]
    have hcomap : (⋃ i, of A f i '' (of A f i ⁻¹' (J : Set _))) =
        ⋃ i, of A f i '' (J.comap (of A f i) : Set (A i)) :=
      Set.iUnion_congr fun i ↦ congrArg (of A f i '' ·)
        (Set.ext fun _ ↦ (TwoSidedIdeal.mem_comap (of A f i)).symm)
    have hx' : x ∈ closure (⋃ i, of A f i '' (J.comap (of A f i) : Set (A i))) :=
      hcomap ▸ (coe_ideal_eq_closure_iUnion J) ▸ (hx : x ∈ (J : Set _))
    exact closure_mono (TwoSidedIdeal.subset_span (R := CStarInductiveLimit A f)) hx'
  · rw [TwoSidedIdeal.topologicalClosure_le_iff _ _ hJ, TwoSidedIdeal.span_le]
    refine Set.iUnion_subset fun i ↦ ?_
    rintro _ ⟨a, ha, rfl⟩
    exact (TwoSidedIdeal.mem_comap (of A f i)).mp ha

/-- A closed two-sided ideal `J` of `CStarInductiveLimit A f` is `⊥` if and only if every element
of its stage preimage `J.comap (of A f i)` maps to `0` in the inductive limit. -/
theorem ideal_eq_bot_iff (J : TwoSidedIdeal (CStarInductiveLimit A f))
    [IsClosed (J : Set (CStarInductiveLimit A f))] :
    J = ⊥ ↔ ∀ i, ∀ a ∈ J.comap (of A f i), of A f i a = 0 := by
  constructor
  · rintro rfl i a ha
    exact (TwoSidedIdeal.mem_bot _).mp ((TwoSidedIdeal.mem_comap (of A f i)).mp ha)
  · intro h
    refine le_antisymm (fun x hx ↦ ?_) bot_le
    rw [TwoSidedIdeal.mem_bot]
    have hsub : (⋃ i, of A f i '' (of A f i ⁻¹' (J : Set _))) ⊆ ({0} : Set _) := by
      refine Set.iUnion_subset fun i ↦ ?_
      rintro _ ⟨a, ha, rfl⟩
      exact Set.mem_singleton_iff.mpr (h i a ((TwoSidedIdeal.mem_comap (of A f i)).mpr ha))
    have hx' : x ∈ closure ({0} : Set (CStarInductiveLimit A f)) :=
      closure_mono hsub ((coe_ideal_eq_closure_iUnion J) ▸ (hx : x ∈ (J : Set _)))
    simpa only [closure_singleton, Set.mem_singleton_iff] using hx'

/-- A closed two-sided ideal `J` of `CStarInductiveLimit A f` is `⊤` if and only if its preimage at
every stage `A i` is `⊤`. -/
theorem ideal_eq_top_iff (J : TwoSidedIdeal (CStarInductiveLimit A f))
    [hJ : IsClosed (J : Set (CStarInductiveLimit A f))] :
    J = ⊤ ↔ ∀ i, J.comap (of A f i) = ⊤ := by
  constructor
  · rintro rfl i
    ext a
    simp [TwoSidedIdeal.mem_comap]
  · intro h
    rw [eq_top_iff]
    intro x _
    have hrange : (⋃ i, Set.range (of A f i)) ⊆ (J : Set (CStarInductiveLimit A f)) := by
      refine Set.iUnion_subset fun i ↦ ?_
      rintro _ ⟨a, rfl⟩
      have ha : a ∈ J.comap (of A f i) := by rw [h i]; trivial
      exact (TwoSidedIdeal.mem_comap (of A f i)).mp ha
    exact SetLike.mem_coe.mp (hJ.closure_eq ▸ closure_mono hrange (dense_iUnion_range_of A f x))

/-- **Simplicity of C⋆-inductive limits (cofinal version, Blackadar II.8.2.5)**: if cofinally many
stages `A j` have no closed two-sided ideals other than `⊥` and `⊤`, then every closed two-sided
ideal `J` of `CStarInductiveLimit A f` is `⊥` or `⊤` (even for noninjective transition maps). -/
theorem eq_bot_or_top_of_isClosed_cofinal
    (hcofinal : ∀ i, ∃ j, i ≤ j ∧
      ∀ I : TwoSidedIdeal (A j), IsClosed (I : Set (A j)) → I = ⊥ ∨ I = ⊤)
    (J : TwoSidedIdeal (CStarInductiveLimit A f))
    [hJ : IsClosed (J : Set (CStarInductiveLimit A f))] :
    J = ⊥ ∨ J = ⊤ := by
  by_cases hbot : J = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨i₀, a₀, ha₀J, ha₀_ne⟩ : ∃ i₀, ∃ a₀ ∈ J.comap (of A f i₀), of A f i₀ a₀ ≠ 0 := by
      by_contra! hall
      exact hbot ((ideal_eq_bot_iff J).mpr hall)
    rw [ideal_eq_top_iff]
    intro k
    obtain ⟨m, hi₀m, hkm⟩ := exists_ge_ge i₀ k
    obtain ⟨j, hmj, hsimple_j⟩ := hcofinal m
    have hi₀j : i₀ ≤ j := hi₀m.trans hmj
    have hkj : k ≤ j := hkm.trans hmj
    let Jj : TwoSidedIdeal (A j) := J.comap (of A f j)
    have hJj_closed : IsClosed (Jj : Set (A j)) := by
      have hset : (Jj : Set (A j)) = of A f j ⁻¹' (J : Set _) :=
        Set.ext fun _ ↦ TwoSidedIdeal.mem_comap (of A f j)
      exact hset ▸ hJ.preimage (continuous_of j)
    have hb_mem : f i₀ j hi₀j a₀ ∈ Jj := by
      rw [TwoSidedIdeal.mem_comap, of_f hi₀j]
      exact (TwoSidedIdeal.mem_comap (of A f i₀)).mp ha₀J
    have hb_ne : f i₀ j hi₀j a₀ ≠ 0 := fun h0 ↦
      ha₀_ne (by rw [← of_f hi₀j, h0, map_zero])
    have hJj_ne_bot : Jj ≠ ⊥ := fun hJj_bot ↦
      hb_ne ((TwoSidedIdeal.mem_bot _).mp (hJj_bot ▸ hb_mem))
    have hJj_top : Jj = ⊤ := (hsimple_j Jj hJj_closed).resolve_left hJj_ne_bot
    ext y
    simp only [TwoSidedIdeal.mem_top, iff_true, TwoSidedIdeal.mem_comap]
    rw [← of_f hkj]
    have hy : f k j hkj y ∈ Jj := by rw [hJj_top]; trivial
    exact (TwoSidedIdeal.mem_comap (of A f j)).mp hy

/-- **Simplicity of C⋆-inductive limits (Blackadar II.8.2.5)**: if every stage `A i` has no closed
two-sided ideals other than `⊥` and `⊤`, then every closed two-sided ideal of
`CStarInductiveLimit A f` is `⊥` or `⊤`. -/
theorem eq_bot_or_top_of_isClosed
    (hsimple : ∀ i (I : TwoSidedIdeal (A i)), IsClosed (I : Set (A i)) → I = ⊥ ∨ I = ⊤)
    (J : TwoSidedIdeal (CStarInductiveLimit A f))
    [IsClosed (J : Set (CStarInductiveLimit A f))] :
    J = ⊥ ∨ J = ⊤ :=
  eq_bot_or_top_of_isClosed_cofinal (fun i ↦ ⟨i, le_rfl, hsimple i⟩) J

/-- Specialization to algebraically simple stages (`IsSimpleRing (A i)`, e.g. matrix algebras in
UHF and CAR algebras): every closed two-sided ideal of `CStarInductiveLimit A f` is `⊥` or `⊤`. -/
theorem eq_bot_or_top_of_isClosed_of_isSimpleRing [∀ i, IsSimpleRing (A i)]
    (J : TwoSidedIdeal (CStarInductiveLimit A f))
    [IsClosed (J : Set (CStarInductiveLimit A f))] :
    J = ⊥ ∨ J = ⊤ :=
  eq_bot_or_top_of_isClosed (fun _ I _ ↦ eq_bot_or_eq_top I) J

end TauCeti.CStarInductiveLimit
