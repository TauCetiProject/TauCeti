/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.LinearAlgebra.Countable
import TauCeti.Algebra.Module.Lattice
import TauCeti.LinearAlgebra.Complex.Determinant
import TauCeti.LinearAlgebra.FreeModule.Int

/-!
# The index of a lattice in its preimage under a linear map

Let `L` be a full lattice in a real normed space `E` and `f` a linear endomorphism of `E` with
`f L ⊆ L`. Then `L` lies in its preimage `f⁻¹ L = ZLattice.comap ℝ L f`. The determinant of `f` is
the integer determinant of its restriction to `L` (`ZLattice.det_eq_intCast_det_restrict`; in
infinite dimension both are `1` by convention). When `E` is finite-dimensional, the index of `L` in
`f⁻¹ L`, in the sense of `Nat.card`, is `|det f|` (`ZLattice.natCard_quotient_comap_eq_abs_det`).
When `det f ≠ 0`, `f` maps `f⁻¹ L` onto `L` and `L` onto `f L`, so the relative index of `L` in
`f⁻¹ L` is that of `f L` in `L`, the absolute value of the determinant of the integer matrix of `f`
on a `ℤ`-basis of `L` (`LinearMap.index_range_eq_natAbs_det_toMatrix`), and the quotient is finite
(`ZLattice.finite_quotient_comap_of_det_ne_zero`). When `det f = 0`, the quotient `f⁻¹ L / L` is
infinite (`ZLattice.infinite_quotient_comap_of_det_eq_zero`, for any discrete subgroup `L`): the
preimage contains the uncountable kernel of `f` while `L` is countable. Its `Nat.card` is then `0`,
which is `|det f|`.

Let now `E` be a finite-dimensional complex normed space, `L` a full lattice in `E` and `f` a
complex linear endomorphism with `f L ⊆ L`. The real determinant of `f` is `|det f|²`, so
`Nat.card (f⁻¹ L / L) = normSq (det f)` (`ZLattice.natCard_quotient_comap_eq_normSq_det`), and the
quotient is finite when `det f ≠ 0` (`ZLattice.finite_quotient_comap_complex_of_det_ne_zero`). When
`det f ≠ 0`, this is the order of the kernel of the endomorphism of the complex torus `E / L`
induced by `f`; when `det f = 0`, that kernel is infinite and both sides are `0`.

## Main results

* `ZLattice.det_eq_intCast_det_restrict`: `det f` is the determinant of `f` restricted to `L`.
* `ZLattice.infinite_quotient_comap_of_det_eq_zero`: `f⁻¹ L / L` is infinite when `det f = 0`.
* `ZLattice.natCard_quotient_comap_eq_abs_det`: `Nat.card (f⁻¹ L / L) = |det f|` for a full
  lattice `L` in finite dimension with `f L ⊆ L`.
* `ZLattice.finite_quotient_comap_of_det_ne_zero`: `f⁻¹ L / L` is finite when `det f ≠ 0`.
* `ZLattice.natCard_quotient_comap_eq_normSq_det`,
  `ZLattice.finite_quotient_comap_complex_of_det_ne_zero`: `Nat.card (f⁻¹ L / L) = |det f|²`, and
  finiteness when `det f ≠ 0`, for a full lattice `L` in a finite-dimensional complex space and a
  complex linear `f` with `f L ⊆ L`.
-/

public section

open Module

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] {f : E →ₗ[ℝ] E}

/-- A full lattice in an infinite-dimensional space is not finitely generated: a finite set
generating `L` over `ℤ` would span `E` over `ℝ`. -/
private theorem not_moduleFinite_of_not_finiteDimensional [IsZLattice ℝ L]
    (hE : ¬FiniteDimensional ℝ E) : ¬Module.Finite ℤ L := by
  intro hL
  obtain ⟨t, ht⟩ := (Submodule.fg_top L).mp (Module.finite_def.mp hL)
  have htop : Submodule.span ℝ (t : Set E) = ⊤ := by
    rw [eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := L)]
    refine Submodule.span_le.mpr fun x hx ↦ ?_
    rw [← ht] at hx
    exact Submodule.span_le_restrictScalars ℤ ℝ _ hx
  exact hE (Module.finite_def.mpr ⟨t, htop⟩)

/-- **The determinant of a lattice-preserving map is an integer.** If `f L ⊆ L` for a full lattice
`L`, then `det f` is the determinant of the `ℤ`-linear restriction of `f` to `L`. In infinite
dimension both sides are `1` by convention. -/
theorem det_eq_intCast_det_restrict [IsZLattice ℝ L] (hf : ∀ l ∈ L, f l ∈ L) :
    LinearMap.det f = ((LinearMap.det ((f.restrictScalars ℤ).restrict hf) : ℤ) : ℝ) := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · rw [LinearMap.det_eq_one_of_not_module_finite hE,
      LinearMap.det_eq_one_of_not_module_finite (not_moduleFinite_of_not_finiteDimensional L hE),
      Int.cast_one]
  let b := Free.chooseBasis ℤ L
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix (b.ofZLatticeBasis ℝ L),
    ← eq_intCast (Int.castRingHom ℝ), RingHom.map_det]
  congr 1
  ext i j
  -- The restricted map sends `b j` to the lattice point `f (b j)`.
  have hj : (f.restrictScalars ℤ).restrict hf (b j) = ⟨f (b j), hf _ (b j).property⟩ :=
    Subtype.ext (LinearMap.coe_restrict_apply (f := f.restrictScalars ℤ) hf (b j))
  simp only [LinearMap.toMatrix_apply, Basis.ofZLatticeBasis_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, eq_intCast, hj]
  exact b.ofZLatticeBasis_repr_apply ℝ L ⟨f (b j), hf _ (b j).property⟩ i

/-- **A singular map has a preimage of infinite index.** If `det f = 0`, the quotient `f⁻¹ L / L`
is infinite: `f⁻¹ L` contains the kernel of `f`, a nonzero real vector space, hence is uncountable,
while `L` is countable. (In infinite dimension `det f = 1` by convention.) -/
theorem infinite_quotient_comap_of_det_eq_zero (hdet : LinearMap.det f = 0) :
    Infinite (ZLattice.comap ℝ L f ⧸ L.submoduleOf (ZLattice.comap ℝ L f)) := by
  have : FiniteDimensional ℝ E := by
    by_contra hE
    rw [LinearMap.det_eq_one_of_not_module_finite hE] at hdet
    exact one_ne_zero hdet
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.bot_lt_ker_of_det_eq_zero hdet).ne'
  set N := ZLattice.comap ℝ L f
  refine not_finite_iff_infinite.mp fun _ ↦ ?_
  -- `L ∩ N` embeds into the countable group `L`, so `N ≃ (N / (L ∩ N)) × (L ∩ N)` is countable.
  have : Countable L := Countable.of_moduleFinite (R := ℤ)
  have : Countable (L.submoduleOf N).toAddSubgroup :=
    Function.Injective.countable
      (f := fun x : (L.submoduleOf N).toAddSubgroup ↦ (⟨x.val.val, x.property⟩ : L))
      fun x y h ↦ by ext; simpa using congrArg Subtype.val h
  have : Finite (N ⧸ (L.submoduleOf N).toAddSubgroup) := ‹Finite (N ⧸ L.submoduleOf N)›
  have : Countable N := (AddSubgroup.addGroupEquivQuotientProdAddSubgroup
    (s := (L.submoduleOf N).toAddSubgroup)).injective.countable
  -- `t ↦ t • v` embeds `ℝ` into `N`.
  have hmem (t : ℝ) : t • v ∈ N := by
    rw [← SetLike.mem_coe, ZLattice.coe_comap, Set.mem_preimage, map_smul,
      LinearMap.mem_ker.mp hv, smul_zero, SetLike.mem_coe]
    exact L.zero_mem
  have : Countable ℝ := Function.Injective.countable (f := fun t : ℝ ↦ (⟨t • v, hmem t⟩ : N))
    fun s t h ↦ smul_left_injective ℝ hv0 (congrArg Subtype.val h)
  exact Cardinal.not_countable_real Set.countable_univ

omit [DiscreteTopology L] in
/-- The relative index of `L` in its preimage under a bijective `f` with `f L ⊆ L` is the index of
the image of the restriction of `f` to `L`. -/
private theorem natCard_quotient_comap_eq_index_range (hf : ∀ l ∈ L, f l ∈ L)
    (hbij : Function.Bijective f) :
    Nat.card (ZLattice.comap ℝ L f ⧸ L.submoduleOf (ZLattice.comap ℝ L f)) =
      (LinearMap.range ((f.restrictScalars ℤ).restrict hf)).toAddSubgroup.index := by
  -- The image of `L` is the range of the restriction of `f` to `L`, as a subgroup of `L`.
  have hrange : (LinearMap.range ((f.restrictScalars ℤ).restrict hf)).toAddSubgroup =
      (L.toAddSubgroup.map f.toAddMonoidHom).addSubgroupOf L.toAddSubgroup := by
    rw [LinearMap.range_restrict (f.restrictScalars ℤ) hf]
    ext x
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_comap, AddSubgroup.mem_addSubgroupOf,
      Submodule.mem_map, AddSubgroup.mem_map]
    simp only [Submodule.subtype_apply, LinearMap.restrictScalars_apply,
      LinearMap.toAddMonoidHom_coe, Submodule.mem_toAddSubgroup]
  calc Nat.card (ZLattice.comap ℝ L f ⧸ L.submoduleOf (ZLattice.comap ℝ L f))
      = L.toAddSubgroup.relIndex (ZLattice.comap ℝ L f).toAddSubgroup :=
        Submodule.natCard_quotient_submoduleOf L _
    _ = (L.toAddSubgroup.map f.toAddMonoidHom).relIndex
          ((ZLattice.comap ℝ L f).toAddSubgroup.map f.toAddMonoidHom) :=
        (AddSubgroup.relIndex_map_map_of_injective _ _ hbij.1).symm
    _ = (L.toAddSubgroup.map f.toAddMonoidHom).relIndex L.toAddSubgroup := by
        rw [ZLattice.comap_toAddSubgroup, AddSubgroup.map_comap_eq_self_of_surjective hbij.2]
    _ = (LinearMap.range ((f.restrictScalars ℤ).restrict hf)).toAddSubgroup.index := by
        rw [AddSubgroup.relIndex, hrange]

/-- **The index of a lattice in its preimage.** If `f L ⊆ L` for a full lattice `L` in a
finite-dimensional real normed space `E`, then `L` has index `|det f|` in its preimage `f⁻¹ L`,
in the sense of `Nat.card`: when `det f = 0` the quotient is infinite and both sides are `0`. -/
theorem natCard_quotient_comap_eq_abs_det [FiniteDimensional ℝ E] [IsZLattice ℝ L]
    (hf : ∀ l ∈ L, f l ∈ L) :
    (Nat.card (ZLattice.comap ℝ L f ⧸ L.submoduleOf (ZLattice.comap ℝ L f)) : ℝ) =
      |LinearMap.det f| := by
  rcases eq_or_ne (LinearMap.det f) 0 with hdet | hdet
  · have := infinite_quotient_comap_of_det_eq_zero L hdet
    rw [hdet, abs_zero, Nat.card_eq_zero_of_infinite, Nat.cast_zero]
  have hbij : Function.Bijective f := (Module.End.isUnit_iff f).mp
    ((LinearMap.isUnit_iff_isUnit_det f).mpr (isUnit_iff_ne_zero.mpr hdet))
  let b := Free.chooseBasis ℤ L
  -- The index of the image is `|det|` of the integer matrix of `f` on a basis of `L`.
  rw [natCard_quotient_comap_eq_index_range L hf hbij,
    LinearMap.index_range_eq_natAbs_det_toMatrix b b, Nat.cast_natAbs, Int.cast_abs,
    LinearMap.det_toMatrix, ← det_eq_intCast_det_restrict L hf]

/-- **A nonsingular map has a preimage of finite index.** If `f L ⊆ L` for a full lattice `L` in a
finite-dimensional real normed space and `det f ≠ 0`, the quotient `f⁻¹ L / L` is finite. -/
theorem finite_quotient_comap_of_det_ne_zero [FiniteDimensional ℝ E] [IsZLattice ℝ L]
    (hf : ∀ l ∈ L, f l ∈ L) (hdet : LinearMap.det f ≠ 0) :
    Finite (ZLattice.comap ℝ L f ⧸ L.submoduleOf (ZLattice.comap ℝ L f)) := by
  refine Nat.finite_of_card_ne_zero fun h0 ↦ hdet (abs_eq_zero.mp ?_)
  rw [← natCard_quotient_comap_eq_abs_det L hf, h0, Nat.cast_zero]

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {f : E →ₗ[ℂ] E}

omit [FiniteDimensional ℂ E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- The preimage of `L` under a complex linear map does not depend on the field of scalars. -/
private theorem comap_complex_eq_comap_restrictScalars :
    ZLattice.comap ℂ L f = ZLattice.comap ℝ L (f.restrictScalars ℝ) := by
  ext x
  simp [← SetLike.mem_coe, ZLattice.coe_comap]

/-- **The index of a lattice in its preimage, complex case.** If `f L ⊆ L` for a full lattice `L`
in a finite-dimensional complex normed space `E` and a complex linear `f`, then `L` has index
`|det f|² = normSq (det f)` in its preimage `f⁻¹ L`, in the sense of `Nat.card`: both sides are
`0` when `det f = 0`. -/
theorem natCard_quotient_comap_eq_normSq_det (hf : ∀ l ∈ L, f l ∈ L) :
    (Nat.card (ZLattice.comap ℂ L f ⧸ L.submoduleOf (ZLattice.comap ℂ L f)) : ℝ) =
      Complex.normSq (LinearMap.det f) := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  rw [comap_complex_eq_comap_restrictScalars,
    natCard_quotient_comap_eq_abs_det L (f := f.restrictScalars ℝ) hf,
    abs_of_nonneg (LinearMap.det_restrictScalars_nonneg f), LinearMap.det_restrictScalars_eq_normSq]

/-- **A nonsingular map has a preimage of finite index, complex case.** If `f L ⊆ L` for a full
lattice `L` in a finite-dimensional complex normed space, `f` is complex linear and `det f ≠ 0`,
the quotient `f⁻¹ L / L` is finite. -/
theorem finite_quotient_comap_complex_of_det_ne_zero (hf : ∀ l ∈ L, f l ∈ L)
    (hdet : LinearMap.det f ≠ 0) :
    Finite (ZLattice.comap ℂ L f ⧸ L.submoduleOf (ZLattice.comap ℂ L f)) := by
  refine Nat.finite_of_card_ne_zero fun h0 ↦ hdet (Complex.normSq_eq_zero.mp ?_)
  rw [← natCard_quotient_comap_eq_normSq_det L hf, h0, Nat.cast_zero]

end Complex

end ZLattice
