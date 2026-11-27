/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BracketNorm
public import TauCeti.Algebra.Lie.InvariantForm.Positive
public import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# The norm of the Lie bracket for an invariant inner product

Let `L` be a finite-dimensional real Lie algebra with an invariant inner product `B`, a reflexive
bilinear form with positive definite diagonal and `B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆`, for instance the
Lie algebra of a compact group with an `Ad`-invariant inner product. The centre of `L` and the
derived algebra `[L, L]` are then orthogonal complementary ideals, and `[L, L]` is semisimple
(`LinearMap.BilinForm.isSemisimple_derivedSeries_one_of_anisotropic`), so it is the sum of its
finitely many simple ideals, which are pairwise orthogonal
(`LinearMap.BilinForm.le_orthogonal_of_isAtom`). Brackets across distinct summands vanish and
squared norms add over the summands, so the norm of the Lie bracket
`γ₀(L, B) = max {|⁅X, Y⁆| : |X| ≤ 1, |Y| ≤ 1}` (`QuadraticMap.lieBracketNorm`) is the largest of
the norms `γ₀(I, B|_I)` of the simple ideals `I` of `[L, L]`, and is `0` when `L` is abelian.

The structure constant of a compact Lie algebra is therefore computed on a single simple factor,
and a maximising pair `X, Y` can be taken inside one simple ideal. This is how the structure
constant enters Yang–Mills theory, where extremal configurations such as an instanton are placed
in one simple factor of the Lie algebra.

## Main results

* `LinearMap.BilinForm.lieBracketNorm_toQuadraticMap_eq_iSup_of_isSemisimple`: on a semisimple Lie
  algebra, `γ₀` is the supremum of the `γ₀(I)` over the atoms `I` of the ideals.
* `LinearMap.BilinForm.lieBracketNorm_toQuadraticMap_comp_derivedSeries_incl`: `γ₀(L)` equals the
  norm of the bracket of the derived algebra `[L, L]`.
* `LinearMap.BilinForm.lieBracketNorm_toQuadraticMap_eq_iSup`: `γ₀(L)` is the supremum of the
  `γ₀(I)` over the simple ideals `I` of `[L, L]`, the atoms of its ideals.
* `LinearMap.BilinForm.exists_isAtom_lieBracketNorm_toQuadraticMap_eq`: for non-abelian `L` the
  supremum is attained by a simple ideal of `[L, L]`.

## References

* S. Gursky, C. Kelleher and J. Streets, *A conformally invariant gap theorem in Yang–Mills
  theory*, Comm. Math. Phys. 361 (2018), arXiv:1708.01157, Definition 2.3.
* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), arXiv:1709.08604, Section 6.
-/

public section

noncomputable section

open LieAlgebra

namespace LinearMap.BilinForm

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- If two disjoint ideals are orthogonal for a reflexive invariant form with nonnegative diagonal,
then the bracket bound `B ⁅X, Y⁆ ⁅X, Y⁆ ≤ c² B X X B Y Y` on each of them gives the same bound on
their sum: brackets across the two ideals vanish, and the squared norms add. -/
private theorem apply_lie_le_of_mem_sup {B : LinearMap.BilinForm ℝ L} (hrefl : B.IsRefl)
    (hinv : B.lieInvariant L) (hnonneg : ∀ X, 0 ≤ B X X) {I J : LieIdeal ℝ L}
    (hIJ : Disjoint I J) (horth : I ≤ LieAlgebra.InvariantForm.orthogonal B hinv J) {c : ℝ}
    (hI : ∀ X ∈ I, ∀ Y ∈ I, B ⁅X, Y⁆ ⁅X, Y⁆ ≤ c ^ 2 * B X X * B Y Y)
    (hJ : ∀ X ∈ J, ∀ Y ∈ J, B ⁅X, Y⁆ ⁅X, Y⁆ ≤ c ^ 2 * B X X * B Y Y) :
    ∀ X ∈ I ⊔ J, ∀ Y ∈ I ⊔ J, B ⁅X, Y⁆ ⁅X, Y⁆ ≤ c ^ 2 * B X X * B Y Y := by
  have hadd {u v : L} (hu : u ∈ I) (hv : v ∈ J) : B (u + v) (u + v) = B u u + B v v := by
    have h₁ : B v u = 0 := (LieAlgebra.InvariantForm.mem_orthogonal _ _ _ _).mp (horth hu) v hv
    simp [h₁, hrefl _ _ h₁]
  have hcross {u v : L} (hu : u ∈ I) (hv : v ∈ J) : ⁅u, v⁆ = 0 :=
    (LieSubmodule.mem_bot _).mp <| hIJ.le_bot
      ⟨lie_mem_left ℝ L I u v hu, lie_mem_right ℝ L J u v hv⟩
  intro X hX Y hY
  obtain ⟨a, ha, b, hb, rfl⟩ := (LieSubmodule.mem_sup _ _ _).mp hX
  obtain ⟨a', ha', b', hb', rfl⟩ := (LieSubmodule.mem_sup _ _ _).mp hY
  have hlie : ⁅a + b, a' + b'⁆ = ⁅a, a'⁆ + ⁅b, b'⁆ := by
    rw [add_lie, lie_add, lie_add, hcross ha hb', ← lie_skew b a', hcross ha' hb]
    abel
  rw [hlie, hadd (lie_mem_left ℝ L I a a' ha) (lie_mem_left ℝ L J b b' hb), hadd ha hb,
    hadd ha' hb']
  have h₁ := hI a ha a' ha'
  have h₂ := hJ b hb b' hb'
  have := mul_nonneg (mul_nonneg (sq_nonneg c) (hnonneg a)) (hnonneg b')
  have := mul_nonneg (mul_nonneg (sq_nonneg c) (hnonneg b)) (hnonneg a')
  nlinarith

variable [FiniteDimensional ℝ L] {B : LinearMap.BilinForm ℝ L}

/-- The bracket bound of `QuadraticMap.apply_lie_le` for the restriction of `B` to an ideal
`I`, read on the elements of `I` in `L`, with any constant `c` at least the norm of the bracket of
`I`. -/
private theorem apply_lie_le_of_mem (hpos : B.toQuadraticMap.PosDef) (I : LieIdeal ℝ L) {c : ℝ}
    (hc : (B.toQuadraticMap.comp I.incl.toLinearMap).lieBracketNorm ≤ c) {X Y : L} (hX : X ∈ I)
    (hY : Y ∈ I) : B ⁅X, Y⁆ ⁅X, Y⁆ ≤ c ^ 2 * B X X * B Y Y := by
  have h := QuadraticMap.apply_lie_le (hpos.comp _ I.incl_injective) ⟨X, hX⟩ ⟨Y, hY⟩
  simp only [QuadraticMap.comp_apply, LieHom.coe_toLinearMap, LieHom.map_lie,
    LieIdeal.incl_apply, BilinMap.toQuadraticMap_apply] at h
  have hX₀ : 0 ≤ B X X := by simpa using hpos.nonneg X
  have hY₀ : 0 ≤ B Y Y := by simpa using hpos.nonneg Y
  have hγ := QuadraticMap.lieBracketNorm_nonneg (B.toQuadraticMap.comp I.incl.toLinearMap)
  exact h.trans (by gcongr)

/-- **The norm of the Lie bracket of a semisimple Lie algebra is the largest norm of its simple
ideals**: for a reflexive invariant form `B` with positive definite diagonal on a
finite-dimensional semisimple real Lie algebra `L`, `γ₀(L, B)` is the supremum of the norms
`γ₀(I, B|_I)` of the brackets of the atoms `I` of the ideals of `L`. -/
theorem lieBracketNorm_toQuadraticMap_eq_iSup_of_isSemisimple [IsSemisimple ℝ L]
    (hrefl : B.IsRefl) (hpos : B.toQuadraticMap.PosDef) (hinv : B.lieInvariant L) :
    B.toQuadraticMap.lieBracketNorm =
      ⨆ I : {I : LieIdeal ℝ L // IsAtom I},
        (B.toQuadraticMap.comp I.val.incl.toLinearMap).lieBracketNorm := by
  set c := ⨆ I : {I : LieIdeal ℝ L // IsAtom I},
    (B.toQuadraticMap.comp I.val.incl.toLinearMap).lieBracketNorm
  refine le_antisymm ?_ (Real.iSup_le (fun I ↦ QuadraticMap.lieBracketNorm_comp_le hpos _)
    (QuadraticMap.lieBracketNorm_nonneg _))
  have hbdd : BddAbove (Set.range fun I : {I : LieIdeal ℝ L // IsAtom I} ↦
      (B.toQuadraticMap.comp I.val.incl.toLinearMap).lieBracketNorm) :=
    ⟨_, by rintro _ ⟨I, rfl⟩; exact QuadraticMap.lieBracketNorm_comp_le hpos _⟩
  have hnonneg (X : L) : 0 ≤ B X X := by simpa using hpos.nonneg X
  -- The bound with constant `c` holds on the sum of every finite set of atoms, by induction.
  have key (s : Finset (LieIdeal ℝ L)) (hs : (s : Set (LieIdeal ℝ L)) ⊆ {I | IsAtom I}) :
      ∀ X ∈ s.sup _root_.id, ∀ Y ∈ s.sup _root_.id, B ⁅X, Y⁆ ⁅X, Y⁆ ≤ c ^ 2 * B X X * B Y Y := by
    classical
    induction s using Finset.induction_on with
    | empty =>
      intro X hX Y _
      rw [Finset.sup_empty] at hX
      simp [(LieSubmodule.mem_bot (R := ℝ) (L := L) X).mp hX]
    | insert I s hIs ih =>
      rw [Finset.coe_insert, Set.insert_subset_iff] at hs
      have hdisj : Disjoint I (s.sup _root_.id) := by
        rw [Finset.sup_id_eq_sSup]
        exact IsSemisimple.sSupIndep_isAtom.disjoint_sSup hs.1 hs.2 hIs
      rw [Finset.sup_insert]
      exact apply_lie_le_of_mem_sup hrefl hinv hnonneg hdisj
        (le_orthogonal_of_isAtom B hinv hs.1 (IsSemisimple.non_abelian_of_isAtom I hs.1) hdisj)
        (fun X hX Y hY ↦ apply_lie_le_of_mem hpos I (le_ciSup hbdd ⟨I, hs.1⟩) hX hY)
        (ih hs.2)
  -- There are finitely many atoms, and their supremum is `L`.
  have hfin := WellFoundedGT.finite_of_sSupIndep (IsSemisimple.sSupIndep_isAtom (R := ℝ) (L := L))
  have htop : hfin.toFinset.sup _root_.id = ⊤ := by
    rw [Finset.sup_id_eq_sSup, Set.Finite.coe_toFinset, IsSemisimple.sSup_atoms_eq_top]
  refine QuadraticMap.lieBracketNorm_le_of_forall_apply_le hpos.nonneg
    (Real.iSup_nonneg fun _ ↦ QuadraticMap.lieBracketNorm_nonneg _) fun X Y ↦ ?_
  have h := key _ (by simp) X (htop ▸ LieSubmodule.mem_top X) Y (htop ▸ LieSubmodule.mem_top Y)
  simpa using h

/-- **The norm of the Lie bracket is that of the derived algebra**: for a reflexive invariant form
`B` with positive definite diagonal on a finite-dimensional real Lie algebra `L`, the norm of the
bracket of `[L, L]` for the restriction of `B` is `γ₀(L, B)`. The centre brackets trivially and is
orthogonal to `[L, L]`. -/
theorem lieBracketNorm_toQuadraticMap_comp_derivedSeries_incl (hrefl : B.IsRefl)
    (hpos : B.toQuadraticMap.PosDef) (hinv : B.lieInvariant L) :
    (B.toQuadraticMap.comp (derivedSeries ℝ L 1).incl.toLinearMap).lieBracketNorm =
      B.toQuadraticMap.lieBracketNorm := by
  set D := derivedSeries ℝ L 1
  refine le_antisymm (QuadraticMap.lieBracketNorm_comp_le hpos _) ?_
  have hcompl := B.isCompl_center_derivedSeries_one_of_anisotropic hrefl hpos.anisotropic hinv
  have hnonneg (X : L) : 0 ≤ B X X := by simpa using hpos.nonneg X
  have horth : center ℝ L ≤ LieAlgebra.InvariantForm.orthogonal B hinv D :=
    (orthogonal_derivedSeries_one_eq_center B
      (nondegenerate_of_anisotropic B hpos.anisotropic).2 hinv).ge
  have h := apply_lie_le_of_mem_sup hrefl hinv hnonneg hcompl.disjoint horth
    (c := (B.toQuadraticMap.comp D.incl.toLinearMap).lieBracketNorm)
    (fun X hX Y _ ↦ by
      rw [← lie_skew, (LieModule.mem_maxTrivSubmodule ℝ L L X).mp hX Y, neg_zero, map_zero]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (hnonneg X)) (hnonneg Y))
    (fun X hX Y hY ↦ apply_lie_le_of_mem hpos D le_rfl hX hY)
  rw [hcompl.sup_eq_top] at h
  refine QuadraticMap.lieBracketNorm_le_of_forall_apply_le hpos.nonneg
    (QuadraticMap.lieBracketNorm_nonneg _) fun X Y ↦ ?_
  simpa using h X (LieSubmodule.mem_top X) Y (LieSubmodule.mem_top Y)

/-- **The norm of the Lie bracket is the largest norm of a simple ideal of the derived algebra**:
for a reflexive invariant form `B` with positive definite diagonal on a finite-dimensional real Lie
algebra `L`, `γ₀(L, B)` is the supremum of the norms `γ₀(I, B|_I)` over the atoms `I` of the ideals
of the semisimple algebra `[L, L]`, which are its simple ideals. For abelian `L` there are none, and
both sides are `0`. -/
theorem lieBracketNorm_toQuadraticMap_eq_iSup (hrefl : B.IsRefl) (hpos : B.toQuadraticMap.PosDef)
    (hinv : B.lieInvariant L) :
    B.toQuadraticMap.lieBracketNorm =
      ⨆ I : {I : LieIdeal ℝ (derivedSeries ℝ L 1) // IsAtom I},
        (B.toQuadraticMap.comp
          ((derivedSeries ℝ L 1).incl.comp I.val.incl).toLinearMap).lieBracketNorm := by
  set D := derivedSeries ℝ L 1
  let BD : LinearMap.BilinForm ℝ D := B.compl₁₂ D.incl.toLinearMap D.incl.toLinearMap
  have := B.isSemisimple_derivedSeries_one_of_anisotropic hrefl hpos.anisotropic hinv
  rw [← lieBracketNorm_toQuadraticMap_comp_derivedSeries_incl hrefl hpos hinv]
  exact lieBracketNorm_toQuadraticMap_eq_iSup_of_isSemisimple (B := BD)
    (hrefl.compl₁₂ D.incl.toLinearMap)
    (B.posDef_toQuadraticMap_compl₁₂ hpos D.incl.toLinearMap D.incl_injective)
    (hinv.compl₁₂ D.incl)

/-- **The norm of the Lie bracket is attained on a simple ideal**: for a reflexive invariant form
`B` with positive definite diagonal on a finite-dimensional non-abelian real Lie algebra `L`, some
simple ideal `I` of `[L, L]`, an atom of its ideals, has `γ₀(I, B|_I) = γ₀(L, B)`. -/
theorem exists_isAtom_lieBracketNorm_toQuadraticMap_eq (hrefl : B.IsRefl)
    (hpos : B.toQuadraticMap.PosDef) (hinv : B.lieInvariant L) (hL : ¬IsLieAbelian L) :
    ∃ I : LieIdeal ℝ (derivedSeries ℝ L 1), IsAtom I ∧
      (B.toQuadraticMap.comp ((derivedSeries ℝ L 1).incl.comp I.incl).toLinearMap).lieBracketNorm =
        B.toQuadraticMap.lieBracketNorm := by
  have := B.isSemisimple_derivedSeries_one_of_anisotropic hrefl hpos.anisotropic hinv
  have hpos' := (QuadraticMap.lieBracketNorm_pos_iff hpos).mpr hL
  rw [lieBracketNorm_toQuadraticMap_eq_iSup hrefl hpos hinv] at hpos' ⊢
  -- The supremum is positive, so there is an atom, and finitely many of them.
  have : Nonempty {I : LieIdeal ℝ (derivedSeries ℝ L 1) // IsAtom I} := by
    by_contra h
    have := not_nonempty_iff.mp h
    rw [Real.iSup_of_isEmpty] at hpos'
    exact hpos'.false
  have : Finite {I : LieIdeal ℝ (derivedSeries ℝ L 1) // IsAtom I} :=
    (WellFoundedGT.finite_of_sSupIndep IsSemisimple.sSupIndep_isAtom).to_subtype
  obtain ⟨I, hI⟩ := exists_eq_ciSup_of_finite
    (f := fun I : {I : LieIdeal ℝ (derivedSeries ℝ L 1) // IsAtom I} ↦ (B.toQuadraticMap.comp
      ((derivedSeries ℝ L 1).incl.comp I.val.incl).toLinearMap).lieBracketNorm)
  exact ⟨I.val, I.property, hI⟩

end LinearMap.BilinForm
