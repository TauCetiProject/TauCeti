/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import TauCeti.RingTheory.Length
import TauCeti.RingTheory.Length.Determinant

/-!
# Quotient lengths and squarefreeness in discrete valuation rings

The length of `R/I` for a nonzero ideal of a discrete valuation ring is the exponent of its
maximal ideal in `I`. This is the local length calculation used for different ideals.

An ideal containing `x` has colength at most `v(x)`
(`IsDiscreteValuationRing.length_quotient_le_addVal`).

An element is squarefree exactly when the length of the quotient by its principal
ideal (`Ring.ord`) is at most one. This detects reducedness of principal divisors at
codimension-one points.

A module of finite length over a discrete valuation ring is torsion, and a submodule of finite
colength in `O^ι` is spanned by the rows of a square matrix. The rows of a square matrix `M` span
a submodule of colength `v(det M)`, infinite when `det M = 0`
(`Matrix.length_quotient_span_range_eq_addVal_det`).
-/

public section

namespace Ideal

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The length of the quotient by a nonzero ideal of a discrete valuation ring is its
multiplicity at the maximal ideal. -/
theorem length_quotient_eq_multiplicity (I : Ideal R) (hI : I ≠ ⊥) :
    Module.length R (R ⧸ I) = multiplicity (maximalIdeal R) I := by
  have hgen : Submodule.IsPrincipal.generator I ≠ 0 := by
    intro hzero
    apply hI
    rw [← span_singleton_generator I, hzero, span_singleton_zero]
  rw [← span_singleton_generator I, ← Ring.ord]
  exact (Ring.ord_eq_addVal _).trans
    (TauCeti.IsDiscreteValuationRing.addVal_eq_multiplicity_span_singleton hgen)

end Ideal

namespace TauCeti.Ring

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- In a discrete valuation ring an element is squarefree exactly when the quotient by
its principal ideal has length at most one. -/
theorem squarefree_iff_ord_le_one {f : R} :
    Squarefree f ↔ Ring.ord R f ≤ 1 := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp [Ring.ord_eq_addVal]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf hπ
  rw [Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_def' u hπ n]
  constructor
  · intro h
    obtain h | h := h.of_mul_right.eq_zero_or_one_of_pow_of_not_isUnit hπ.not_isUnit <;>
      simp [h]
  · intro hn
    have hn : n ≤ 1 := by exact_mod_cast hn
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · simp
    · simpa using (associated_unit_mul_left π u u.isUnit).squarefree_iff.mpr hπ.squarefree

end TauCeti.Ring

namespace IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- A module containing an element with trivial annihilator, here the image of an injective map
`O → M`, has infinite length over a discrete valuation ring. -/
theorem length_eq_top_of_injective {M : Type*} [AddCommGroup M] [Module O M] {f : O →ₗ[O] M}
    (hf : Function.Injective f) : Module.length O M = ⊤ :=
  top_le_iff.1 (TauCeti.length_self_eq_top_of_ringKrullDim_pos
    (by rw [ringKrullDim_eq_one O]; exact zero_lt_one) ▸ Module.length_le_of_injective f hf)

/-- A module of finite length over a discrete valuation ring is torsion. -/
theorem isTorsion_of_length_ne_top {M : Type*} [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) : Module.IsTorsion O M := by
  intro x
  by_contra hx
  refine hM (length_eq_top_of_injective (f := LinearMap.toSpanSingleton O M x) fun r s h ↦ ?_)
  rw [← sub_eq_zero]
  by_contra hrs
  exact hx ⟨⟨r - s, mem_nonZeroDivisors_of_ne_zero hrs⟩, by simpa [sub_smul, sub_eq_zero] using h⟩

/-- A submodule of finite colength in `O^ι` is spanned by the rows of a square matrix: it is free
(`O` is a principal ideal domain) and contains `c • O^ι` for some `c ≠ 0`, so it has rank
`card ι`. -/
theorem exists_matrix_span_range_row_eq {ι : Type*} [Finite ι] (R : Submodule O (ι → O))
    (hR : Module.length O ((ι → O) ⧸ R) ≠ ⊤) :
    ∃ M : Matrix ι ι O, Submodule.span O (Set.range M.row) = R := by
  have := Fintype.ofFinite ι
  obtain ⟨c, hc_ann, hc⟩ :=
    Submodule.annihilator_top_inter_nonZeroDivisors (isTorsion_of_length_ne_top hR)
  have hcR : ∀ v : ι → O, c • v ∈ R := fun v ↦ by
    have := Submodule.mem_annihilator.1 hc_ann (R.mkQ v) Submodule.mem_top
    rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hfin : Module.finrank O R = Fintype.card ι := by
    refine le_antisymm ((Submodule.finrank_le R).trans_eq (Module.finrank_fintype_fun_eq_card O)) ?_
    let g : (ι → O) →ₗ[O] R := (LinearMap.lsmul O _ c).codRestrict R hcR
    have hg : Function.Injective g := fun v w h ↦
      smul_right_injective _ hc0 (congrArg Subtype.val h)
    simpa using LinearMap.finrank_le_finrank_of_injective hg
  obtain ⟨k, b₀⟩ := Submodule.basisOfPid (Pi.basisFun O ι) R
  have hk : Fintype.card (Fin k) = Fintype.card ι := by
    rw [← hfin, Module.finrank_eq_card_basis b₀]
  let b : Module.Basis ι O R := b₀.reindex (Fintype.equivOfCardEq hk)
  refine ⟨Matrix.of fun i ↦ (b i : ι → O), ?_⟩
  have hrow : (Matrix.of fun i ↦ (b i : ι → O)).row = R.subtype ∘ b := by
    ext i j
    simp [Matrix.row_apply]
  -- The rows are the basis vectors `b i`, which span `R`.
  rw [hrow, Set.range_comp, Submodule.span_image, b.span_eq]
  simp

/-- An ideal containing `x` has colength at most the valuation of `x`. -/
theorem length_quotient_le_addVal {J : Ideal O} {x : O} (hx : x ∈ J) :
    Module.length O (O ⧸ J) ≤ addVal O x :=
  (TauCeti.length_quotient_anti ((Ideal.span_singleton_le_iff_mem J).2 hx)).trans_eq
    (Ring.ord_eq_addVal x)

/-- If an ideal `J` contains `ϖ ^ m * u` with `ϖ` a uniformizer and `u` a unit, then `O ⧸ J` has
length at most `m`. -/
theorem length_quotient_le_of_pow_mul_mem {ϖ : O} (hϖ : Irreducible ϖ) {J : Ideal O} {m : ℕ}
    {u : O} (hu : IsUnit u) (hJ : ϖ ^ m * u ∈ J) :
    Module.length O (O ⧸ J) ≤ m := by
  refine (length_quotient_le_addVal hJ).trans_eq ?_
  simp [addVal_uniformizer hϖ, (addVal_eq_zero_iff).2 hu]

end IsDiscreteValuationRing

namespace Matrix

open IsDiscreteValuationRing LinearMap

variable {ι O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype ι]
  [DecidableEq ι]

/-- The rows of a singular square matrix over a discrete valuation ring span a submodule of
infinite colength: a nonzero vector `y` with `M y = 0` gives a functional vanishing on the rows,
and a coordinate on which `y` does not vanish embeds `O` in the quotient. -/
theorem length_quotient_span_range_eq_top {M : Matrix ι ι O} (hM : M.det = 0) :
    Module.length O ((ι → O) ⧸ Submodule.span O (Set.range M.row)) = ⊤ := by
  obtain ⟨y, hy, hMy⟩ := M.exists_mulVec_eq_zero_iff.2 hM
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
  set S := Submodule.span O (Set.range M.row)
  have hS : ∀ v ∈ S, v ⬝ᵥ y = 0 := fun v hv ↦ by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      exact congrFun hMy j
    | zero => simp
    | add v w _ _ hv hw => rw [add_dotProduct, hv, hw, add_zero]
    | smul c v _ hv => rw [smul_dotProduct, hv, smul_zero]
  refine length_eq_top_of_injective (f := toSpanSingleton O _ (S.mkQ (Pi.single i 1)))
    fun r s h ↦ ?_
  -- `h` says `r • eᵢ ≡ s • eᵢ` modulo `S`, so `(r - s) • eᵢ ∈ S` is orthogonal to `y`.
  have hrs : (r - s) • Pi.single i (1 : O) ∈ S := by
    rw [sub_smul]
    refine (Submodule.Quotient.eq S).1 ?_
    simpa only [Submodule.Quotient.mk_smul, toSpanSingleton_apply, Submodule.mkQ_apply] using h
  simpa [sub_eq_zero, show y i ≠ 0 from hi] using hS _ hrs

/-- **Cokernel length and determinant for rows.** The rows of a square matrix `M` over a discrete
valuation ring span a submodule of `O^ι` of colength `v(det M)`, both sides infinite when
`det M = 0`. -/
theorem length_quotient_span_range_eq_addVal_det (M : Matrix ι ι O) :
    Module.length O ((ι → O) ⧸ Submodule.span O (Set.range M.row)) = addVal O M.det := by
  rcases eq_or_ne M.det 0 with hM | hM
  · rw [length_quotient_span_range_eq_top hM, hM, AddValuation.map_zero]
  have hrange : Submodule.span O (Set.range M.row) = LinearMap.range Mᵀ.mulVecLin := by
    rw [range_mulVecLin, col_transpose]
  rw [hrange, length_quotient_range_mulVecLin_eq_ord_det _ (by rwa [det_transpose]),
    det_transpose, Ring.ord_eq_addVal]

end Matrix
