/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.LinearAlgebra.FreeModule.Int
import TauCeti.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Torsion of a cokernel with short relations

Let `ι` be a finite type and `Λ₀` a set of vectors of `ℤ^ι` whose `ℓ¹` norms `∑ i, |v i|` are at
most `b ≥ 1`. Then the torsion subgroup of the cokernel `ℤ^ι ⧸ ⟨Λ₀⟩`, which is finite as the
torsion of a finitely generated abelian group (`Module.finite_of_fg_torsion`), has at most
`b ^ #ι` elements. For `ι` a point and `Λ₀ = {b}` the cokernel is `ℤ ⧸ b`, of order `b ^ #ι`.

The proof chooses a subset `s ⊆ Λ₀` that is a basis of the rational span of `Λ₀` and completes it
by unit vectors to a basis `B` of `ℚ^ι`. The lattice `L` spanned by `B` has finite index
`|det B| ≠ 0` (`Matrix.natCard_quotient_range_mulVecLin_eq_natAbs_det`), which by the `ℓ¹` form
of Hadamard's bound (`Matrix.abs_det_le_prod_sum_abs'`) is at most the product of the `ℓ¹` norms
of the members of `s`, the unit vectors having norm `1`. An element of `L` whose class in
`ℤ^ι ⧸ ⟨Λ₀⟩` is torsion lies in the span of `s`, so the image of `L` in the cokernel meets the
torsion trivially, and then the torsion injects into a quotient of `ℤ^ι ⧸ L`. The last step is a
general fact about modules, `Submodule.natCard_torsion_quotient_le_of_disjoint`.

## Main results

* `Submodule.finite_torsion_quotient_of_disjoint`,
  `Submodule.natCard_torsion_quotient_le_of_disjoint`: if `M ⧸ L` is finite and the image of `L`
  in `M ⧸ N` meets the torsion of `M ⧸ N` trivially, that torsion is finite with at most
  `Nat.card (M ⧸ L)` elements.
* `Set.exists_natCard_torsion_quotient_span_le_prod`: the torsion of `ℤ^ι ⧸ ⟨Λ₀⟩` has at most
  as many elements as the product of the `ℓ¹` norms of a subset of `Λ₀` that is a basis of the
  rational span of `Λ₀`.
* `TauCeti.natCard_torsion_quotient_span_le_pow`: if every vector of `Λ₀` has `ℓ¹` norm at most
  `b ≥ 1`, the torsion of `ℤ^ι ⧸ ⟨Λ₀⟩` has at most `b ^ #ι` elements.
* `Matrix.natCard_torsion_quotient_range_mulVecLin_le_pow`: the same bound for the cokernel of an
  integer matrix whose columns have `ℓ¹` norm at most `b ≥ 1`.

## References

* C. Soulé, *Perfect forms and the Vandiver conjecture*, J. reine angew. Math. 517 (1999),
  209–221, Lemma 1 (p. 5 of arXiv:math/9812171v1), which bounds the torsion of such a cokernel by
  the product of the Euclidean norms of a subfamily of `Λ₀` that is a basis of its real span.
* L. Alpöge, the Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/leanprover-community/riemann-hypothesis> (commit
  `40e56bab026552e089d7afcfeff08d2defb9c005`): the bound
  `TauCeti.natCard_torsion_quotient_span_le_pow` is stated there as `UpperTheory.V.KH.cokerTors`
  (`Development/AutomorphicArithmetic/AutomorphicVarieties/TorsionBoundsChains/CokerTors.lean`).
-/

public section

open Module Set

namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If the image of `L` in `M ⧸ N` meets the torsion trivially, the torsion of `M ⧸ N` maps
injectively to `M ⧸ (N ⊔ L)`: the kernel of `M ⧸ N → M ⧸ (N ⊔ L)` is the image of `L`. -/
private theorem injective_factor_domRestrict_torsion {N L : Submodule R M}
    (h : Disjoint (L.map N.mkQ) (torsion R (M ⧸ N))) :
    Function.Injective ((factor (le_sup_left : N ≤ N ⊔ L)).domRestrict (torsion R (M ⧸ N))) := by
  rw [LinearMap.injective_domRestrict_iff]
  simpa [ker_mapQ, map_sup] using h.symm

/-- If `M ⧸ L` is finite and the image of `L` in `M ⧸ N` meets the torsion of `M ⧸ N` trivially,
then that torsion is finite. -/
theorem finite_torsion_quotient_of_disjoint (N : Submodule R M) {L : Submodule R M}
    [Finite (M ⧸ L)]
    (h : Disjoint (L.map N.mkQ) (torsion R (M ⧸ N))) : Finite (torsion R (M ⧸ N)) :=
  have : Finite (M ⧸ (N ⊔ L)) := .of_surjective _ (factor_surjective le_sup_right)
  .of_injective _ (injective_factor_domRestrict_torsion h)

/-- **Torsion of a quotient through a lattice of finite index.** If `M ⧸ L` is finite and the
image of `L` in `M ⧸ N` meets the torsion of `M ⧸ N` trivially, then that torsion has at most
`Nat.card (M ⧸ L)` elements: it injects into `M ⧸ (N ⊔ L)`, a quotient of `M ⧸ L`. -/
theorem natCard_torsion_quotient_le_of_disjoint (N : Submodule R M) {L : Submodule R M}
    [Finite (M ⧸ L)]
    (h : Disjoint (L.map N.mkQ) (torsion R (M ⧸ N))) :
    Nat.card (torsion R (M ⧸ N)) ≤ Nat.card (M ⧸ L) := by
  have : Finite (M ⧸ (N ⊔ L)) := .of_surjective _ (factor_surjective le_sup_right)
  exact (Nat.card_le_card_of_injective _ (injective_factor_domRestrict_torsion h)).trans
    (Nat.card_le_card_of_surjective _ (factor_surjective le_sup_right))

end Submodule

namespace TauCeti

open Submodule

variable {ι : Type*}

/-- The coordinatewise inclusion `ℤ^ι → ℚ^ι`, as a `ℤ`-linear map. -/
private noncomputable abbrev castQ (ι : Type*) : (ι → ℤ) →ₗ[ℤ] ι → ℚ :=
  (Int.castAddHom ℚ).toIntLinearMap.compLeft ι

private theorem castQ_injective : Function.Injective (castQ ι) :=
  Function.Injective.piMap fun _ ↦ Int.cast_injective

/-- Integer vectors whose images in `ℚ^ι` are linearly independent are linearly independent. -/
private theorem linearIndepOn_id_of_castQ {B : Set (ι → ℤ)} (hB : LinearIndepOn ℚ (castQ ι) B) :
    LinearIndepOn ℤ id B :=
  LinearIndependent.of_comp (castQ ι) (v := ((↑) : B → ι → ℤ)) (hB.restrict_scalars' ℤ)

/-- A subset `s ⊆ Λ₀` whose image in `ℚ^ι` is a basis of the rational span of `Λ₀`, completed by
unit vectors to a set `B` whose image is a basis of `ℚ^ι`. -/
private theorem exists_completion [Finite ι] [DecidableEq ι] (Λ₀ : Set (ι → ℤ)) :
    ∃ s B : Set (ι → ℤ), s ⊆ Λ₀ ∧ s ⊆ B ∧ B ⊆ s ∪ range (fun i ↦ Pi.single i 1) ∧
      LinearIndepOn ℚ (castQ ι) B ∧ castQ ι '' Λ₀ ⊆ span ℚ (castQ ι '' s) ∧
      span ℚ (castQ ι '' B) = ⊤ := by
  have := Fintype.ofFinite ι
  obtain ⟨s, hsΛ, -, hΛ, hs⟩ :=
    exists_linearIndepOn_extension (linearIndepOn_empty ℚ (castQ ι)) (empty_subset Λ₀)
  obtain ⟨B, hB, hsB, hspan, hBi⟩ := exists_linearIndepOn_extension hs
    (subset_union_left (t := range fun i ↦ (Pi.single i 1 : ι → ℤ)))
  refine ⟨s, B, hsΛ, hsB, hB, hBi, hΛ, eq_top_iff.mpr ?_⟩
  rw [← (Pi.basisFun ℚ ι).span_eq, span_le]
  rintro _ ⟨i, rfl⟩
  refine hspan ⟨Pi.single i 1, subset_union_right ⟨i, rfl⟩, funext fun j ↦ ?_⟩
  simpa using LinearMap.apply_single (fun _ ↦ (Int.castAddHom ℚ).toIntLinearMap) i j 1

/-- If `s ⊆ Λ₀ ∩ B`, the image of `B` in `ℚ^ι` is linearly independent and the image of `Λ₀` lies in
the rational span of the image of `s`, then an element of the span of `B` whose class modulo
`⟨Λ₀⟩` is torsion lies in `⟨Λ₀⟩`. -/
private theorem disjoint_map_span_torsion {Λ₀ s B : Set (ι → ℤ)} (hsΛ : s ⊆ Λ₀) (hsB : s ⊆ B)
    (hBi : LinearIndepOn ℚ (castQ ι) B) (hΛ : castQ ι '' Λ₀ ⊆ span ℚ (castQ ι '' s)) :
    Disjoint ((span ℤ B).map (span ℤ Λ₀).mkQ) (torsion ℤ ((ι → ℤ) ⧸ span ℤ Λ₀)) := by
  rw [disjoint_def]
  rintro _ ⟨x, hx, rfl⟩ htors
  obtain ⟨⟨a, ha⟩, hax⟩ := (mem_torsion_iff _).mp htors
  rw [Submonoid.smul_def, ← map_smul, ← LinearMap.mem_ker, ker_mkQ] at hax
  rw [← union_sdiff_cancel hsB, span_union] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
  have hyN : y ∈ span ℤ Λ₀ := span_mono hsΛ hy
  suffices z = 0 by rw [this, add_zero, ← LinearMap.mem_ker, ker_mkQ]; exact hyN
  have hzN : a • z ∈ span ℤ Λ₀ := by
    simpa only [smul_add, add_sub_cancel_left] using sub_mem hax (smul_mem _ a hyN)
  have h1 : span ℤ Λ₀ ≤ ((span ℚ (castQ ι '' s)).restrictScalars ℤ).comap (castQ ι) :=
    span_le.mpr fun v hv ↦ hΛ (mem_image_of_mem _ hv)
  have h2 : span ℤ (B \ s) ≤ ((span ℚ (castQ ι '' (B \ s))).restrictScalars ℤ).comap (castQ ι) :=
    span_le.mpr fun v hv ↦ subset_span (mem_image_of_mem _ hv)
  have h3 := ((linearIndepOn_union_iff disjoint_sdiff_right).mp
    ((union_sdiff_cancel hsB).symm ▸ hBi)).2.2
  have h0 : castQ ι (a • z) = castQ ι 0 :=
    (disjoint_def.mp h3 _ (h1 hzN) (h2 (smul_mem _ a hz))).trans (map_zero _).symm
  exact (smul_eq_zero.mp (castQ_injective h0)).resolve_left (nonZeroDivisors.ne_zero ha)

/-- If the image of a set `B ⊆ ℤ^ι` in `ℚ^ι` is linearly independent, `ℚ^ι` has a basis indexed
by `B`, and `B` consists of the members of `s` and of unit vectors, then `ℤ^ι ⧸ ⟨B⟩` is finite
with at most `∏ v ∈ s, ‖v‖₁` elements. -/
private theorem finite_quotient_span_and_natCard_le [Fintype ι] [DecidableEq ι]
    {s : Finset (ι → ℤ)} {B : Set (ι → ℤ)} (hsB : ↑s ⊆ B)
    (hB : B ⊆ ↑s ∪ range (fun i ↦ Pi.single i 1)) (hBi : LinearIndepOn ℚ (castQ ι) B)
    (bas : Basis B ℚ (ι → ℚ)) :
    Finite ((ι → ℤ) ⧸ span ℤ B) ∧
      Nat.card ((ι → ℤ) ⧸ span ℤ B) ≤ ∏ v ∈ s, ∑ i, (v i).natAbs := by
  have : Finite B := Module.Finite.finite_basis bas
  have : Fintype B := Fintype.ofFinite B
  obtain ⟨e⟩ : Nonempty (ι ≃ B) := Finite.card_eq.mp (by
    rw [← finrank_eq_nat_card_basis bas, Module.finrank_fintype_fun_eq_card,
      Nat.card_eq_fintype_card])
  let A : Matrix ι ι ℤ := Matrix.of fun i j ↦ (e j : ι → ℤ) i
  have hcol : A.col = Subtype.val ∘ e := Matrix.col_of _
  have hA : span ℤ B = LinearMap.range A.mulVecLin := by
    rw [Matrix.range_mulVecLin, hcol, e.surjective.range_comp, Subtype.range_coe]
  have hcard : Nat.card ((ι → ℤ) ⧸ span ℤ B) = A.det.natAbs := by
    rw [hA, A.natCard_quotient_range_mulVecLin_eq_natAbs_det]
  have hli : LinearIndependent ℤ A.col :=
    hcol ▸ (linearIndepOn_id_of_castQ hBi).comp e e.injective
  have hdet : A.det ≠ 0 := fun h0 ↦ by
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hv (Matrix.mulVec_injective_iff.mpr hli (hAv.trans (Matrix.mulVec_zero A).symm))
  refine ⟨Nat.finite_of_card_ne_zero (hcard ▸ Int.natAbs_ne_zero.mpr hdet), hcard ▸ ?_⟩
  have hHad := A.abs_det_le_prod_sum_abs'
  simp only [Int.abs_eq_natAbs] at hHad
  refine (Int.ofNat_le.mp (by exact_mod_cast hHad)).trans_eq ?_
  calc ∏ j, ∑ i, (A i j).natAbs = ∏ v : B, ∑ i, (v.val i).natAbs :=
        Fintype.prod_equiv e _ _ fun j ↦ by
          simp only [← Matrix.col_apply A j, hcol, Function.comp_apply]
    _ = ∏ v ∈ B.toFinset, ∑ i, (v i).natAbs :=
        (Finset.prod_subtype _ (fun _ ↦ mem_toFinset) fun v : ι → ℤ ↦ ∑ i, (v i).natAbs).symm
    _ = ∏ v ∈ s, ∑ i, (v i).natAbs := by
      refine (Finset.prod_subset (fun v hv ↦ mem_toFinset.mpr (hsB hv)) fun v hvB hvs ↦ ?_).symm
      obtain ⟨i, rfl⟩ := (hB (mem_toFinset.mp hvB)).resolve_left hvs
      simp [Pi.single_apply, apply_ite Int.natAbs]

/-- **Torsion of a cokernel, sharp form.** For a set `Λ₀` of vectors of `ℤ^ι`, there is a finite
linearly independent subset `s ⊆ Λ₀` with the same rational span as `Λ₀` (so `s` is a basis of the
rational span of `Λ₀`) such that the torsion subgroup of `ℤ^ι ⧸ ⟨Λ₀⟩` has at most
`∏ v ∈ s, ∑ i, |v i|` elements. That torsion subgroup is finite, as is the torsion of any finitely
generated abelian group (`Module.finite_of_fg_torsion`). -/
theorem _root_.Set.exists_natCard_torsion_quotient_span_le_prod [Fintype ι] (Λ₀ : Set (ι → ℤ)) :
    ∃ s : Finset (ι → ℤ), ↑s ⊆ Λ₀ ∧ LinearIndepOn ℤ id (s : Set (ι → ℤ)) ∧
      span ℚ ((fun (v : ι → ℤ) i ↦ (v i : ℚ)) '' s) =
        span ℚ ((fun (v : ι → ℤ) i ↦ (v i : ℚ)) '' Λ₀) ∧
      Nat.card (AddCommGroup.torsion ((ι → ℤ) ⧸ span ℤ Λ₀)) ≤ ∏ v ∈ s, ∑ i, (v i).natAbs := by
  classical
  obtain ⟨s, B, hsΛ, hsB, hB, hBi, hΛ, hspan⟩ := exists_completion Λ₀
  let bas := Basis.mk hBi (by rw [← image_eq_range, hspan])
  have hBfin : B.Finite := Module.Finite.finite_basis bas
  have hs := hBfin.subset hsB
  have hdisj := disjoint_map_span_torsion hsΛ hsB hBi hΛ
  obtain ⟨_, hcard⟩ := finite_quotient_span_and_natCard_le (s := hs.toFinset)
    (by rwa [Finite.coe_toFinset]) (by rwa [Finite.coe_toFinset]) hBi bas
  refine ⟨hs.toFinset, by rwa [Finite.coe_toFinset], ?_, ?_, ?_⟩
  · rw [Finite.coe_toFinset]
    exact linearIndepOn_id_of_castQ (hBi.mono hsB)
  · -- `castQ ι` is the coordinatewise cast `fun v i ↦ (v i : ℚ)`
    rw [Finite.coe_toFinset]
    exact le_antisymm (span_mono (image_mono hsΛ)) (span_le.mpr hΛ)
  · rw [← torsion_int]
    exact ((span ℤ Λ₀).natCard_torsion_quotient_le_of_disjoint hdisj).trans hcard

/-- **Torsion of a cokernel with short relations.** If every vector of a set `Λ₀ ⊆ ℤ^ι` has
`ℓ¹` norm `∑ i, |v i|` at most `b ≥ 1`, the torsion subgroup of `ℤ^ι ⧸ ⟨Λ₀⟩` has at most
`b ^ #ι` elements. That torsion subgroup is finite, as is the torsion of any finitely generated
abelian group (`Module.finite_of_fg_torsion`). -/
theorem natCard_torsion_quotient_span_le_pow [Fintype ι] {Λ₀ : Set (ι → ℤ)} {b : ℕ}
    (hb : 1 ≤ b) (hΛ : ∀ v ∈ Λ₀, ∑ i, (v i).natAbs ≤ b) :
    Nat.card (AddCommGroup.torsion ((ι → ℤ) ⧸ span ℤ Λ₀)) ≤ b ^ Fintype.card ι := by
  obtain ⟨s, hsΛ, hs, -, hcard⟩ := Λ₀.exists_natCard_torsion_quotient_span_le_prod
  have hrank : s.card ≤ Fintype.card ι := by
    simpa using LinearIndependent.finset_card_le_finrank (R := ℤ) hs
  calc _ ≤ ∏ v ∈ s, ∑ i, (v i).natAbs := hcard
    _ ≤ b ^ s.card := Finset.prod_le_pow_card s _ b fun v hv ↦ hΛ v (hsΛ hv)
    _ ≤ b ^ Fintype.card ι := Nat.pow_le_pow_right hb hrank

end TauCeti

/-- **Torsion of the cokernel of an integer matrix with short columns.** If every column of
`A : Matrix ι κ ℤ` has `ℓ¹` norm at most `b ≥ 1`, the torsion subgroup of the cokernel
`ℤ^ι ⧸ A ℤ^κ` has at most `b ^ #ι` elements. -/
theorem Matrix.natCard_torsion_quotient_range_mulVecLin_le_pow {ι κ : Type*} [Fintype ι]
    [Fintype κ] (A : Matrix ι κ ℤ) {b : ℕ} (hb : 1 ≤ b) (hA : ∀ j, ∑ i, (A i j).natAbs ≤ b) :
    Nat.card (AddCommGroup.torsion ((ι → ℤ) ⧸ LinearMap.range A.mulVecLin)) ≤
      b ^ Fintype.card ι := by
  rw [A.range_mulVecLin]
  exact TauCeti.natCard_torsion_quotient_span_le_pow hb (forall_mem_range.mpr hA)
