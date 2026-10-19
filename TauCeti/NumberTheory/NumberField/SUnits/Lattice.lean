/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.NumberField.SUnits.Height
import TauCeti.Algebra.Module.Torsion.Int
import TauCeti.NumberTheory.NumberField.FinitePlace
public import TauCeti.NumberTheory.NumberField.Units.SUnit.FundamentalSystem
import TauCeti.RingTheory.DedekindDomain.SInteger.Rank
import TauCeti.RingTheory.DedekindDomain.ValuationOfNeZero

/-!
# The S-unit lattice

Let `S` be a finite set of finite places of a number field `K`. The image of the `S`-logarithmic
embedding `TauCeti.NumberField.SUnit.logEmbedding S` is the `S`-unit lattice
`TauCeti.NumberField.SUnit.unitLattice S`. This file proves that it is a full `ℤ`-lattice in the
`S`-logarithmic space, of rank `NumberField.Units.rank K + #S`, and identifies it with the
`S`-units modulo torsion. This is the `S`-analogue of Mathlib's `NumberField.Units.unitLattice`;
the covolume of this lattice is what one calls the `S`-regulator.

* **Discreteness.** A bounded `S`-logarithmic image forces a bounded height, and a number field has
  only finitely many elements of bounded height (Northcott's theorem,
  `NumberField.finite_setOfPred_logHeight₁_le`).
* **Spanning.** The ordinary units fill the infinite coordinates, by Mathlib's
  `NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top`. For each `v ∈ S`, raising `v`
  to the class number gives a principal ideal, and a generator is an `S`-unit whose finite
  coordinates vanish except at `v`.
* **The quotient.** The kernel of the `S`-logarithmic embedding is the torsion
  (`TauCeti.NumberField.SUnit.logEmbedding_ker`), so the embedding induces a `ℤ`-linear
  equivalence from the `S`-units modulo torsion onto the lattice.

## Main definitions and results

* `TauCeti.NumberField.SUnit.unitLattice`: the image of the `S`-logarithmic embedding.
* `TauCeti.NumberField.SUnit.unitLattice_inter_ball_finite`: the lattice meets every ball in a
  finite set.
* `TauCeti.NumberField.SUnit.unitLattice_span_eq_top`: the lattice spans the `S`-logarithmic
  space.
* `TauCeti.NumberField.SUnit.unitLattice_rank`: the lattice has rank
  `NumberField.Units.rank K + #S`.
* `TauCeti.NumberField.SUnit.logEmbeddingEquiv`: the equivalence from the `S`-units modulo
  torsion onto the lattice.
* `TauCeti.NumberField.SUnit.basisUnitLattice`: the basis of the lattice given by the
  `S`-logarithmic images of the chosen fundamental system of `S`-units.
* `TauCeti.NumberField.SUnit.isFundSystem_iff_exists_basis`: a family of `S`-units is a
  fundamental system exactly when its `S`-logarithmic images form a basis of the lattice, and
  `TauCeti.NumberField.SUnit.basisOfIsFundSystem` is that basis.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Theorem 1.5.13.
-/

public section

open Finset Height IsDedekindDomain Module NumberField NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem TauCeti.SUnit

namespace TauCeti.NumberField.SUnit

noncomputable section

variable {K : Type*} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The `S`-unit lattice: the image of the `S`-logarithmic embedding, as a `ℤ`-submodule of the
`S`-logarithmic space. -/
def unitLattice : Submodule ℤ (logSpace S) :=
  (logEmbedding S).toIntLinearMap.range

variable {S} in
/-- A vector lies in the `S`-unit lattice exactly when it is the `S`-logarithmic image of an
`S`-unit. -/
theorem mem_unitLattice_iff {y : logSpace S} :
    y ∈ unitLattice S ↔
      ∃ x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K, logEmbedding S (Additive.ofMul x) = y :=
  ⟨fun ⟨x, hx⟩ ↦ ⟨x.toMul, hx⟩, fun ⟨x, hx⟩ ↦ ⟨Additive.ofMul x, hx⟩⟩

/-- The `S`-logarithmic image of an `S`-unit lies in the `S`-unit lattice. -/
@[simp]
theorem logEmbedding_mem_unitLattice (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    logEmbedding S x ∈ unitLattice S :=
  ⟨x, rfl⟩

/-! ### Discreteness -/

open Classical in
/-- The `S`-unit lattice meets every closed ball in a finite set. -/
theorem unitLattice_inter_ball_finite (r : ℝ) :
    ((unitLattice S : Set (logSpace S)) ∩ Metric.closedBall 0 r).Finite := by
  have hfin : {x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K |
      logHeight₁ ((x : Kˣ) : K) ≤ (NumberField.Units.rank K + #S) * r}.Finite :=
    (NumberField.finite_setOfPred_logHeight₁_le (K := K) _).preimage
      ((Units.val_injective.comp Subtype.val_injective).injOn)
  refine ((hfin.image fun x ↦ logEmbedding S (Additive.ofMul x)).subset ?_)
  rintro _ ⟨hy, hr⟩
  obtain ⟨x, rfl⟩ := mem_unitLattice_iff.mp hy
  refine ⟨x, ?_, rfl⟩
  rw [mem_closedBall_zero_iff] at hr
  exact (logHeight₁_le_mul_norm_logEmbedding S x).trans
    (mul_le_mul_of_nonneg_left hr (by positivity))

/-- The `S`-unit lattice is discrete. -/
instance : DiscreteTopology (unitLattice S) := by
  classical
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_singleton_of_finite_mem_nhds 0
    (s := Metric.closedBall (0 : unitLattice S) 1) ?_ ?_
  · exact Metric.closedBall_mem_nhds _ one_pos
  · refine Set.Finite.of_finite_image ?_ Subtype.val_injective.injOn
    refine (unitLattice_inter_ball_finite S 1).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.2, by simpa [mem_closedBall_zero_iff] using hx⟩

/-! ### Spanning -/

/-- For each `v ∈ S` there is an `S`-unit whose finite `S`-logarithmic coordinates vanish
except at `v`, where it is nonzero. It is a generator of a power of `v` that is principal. -/
private theorem exists_logEmbedding_inr (v : S) :
    ∃ x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
      logEmbedding S (Additive.ofMul x) (Sum.inr v) ≠ 0 ∧
        ∀ v' ≠ v, logEmbedding S (Additive.ofMul x) (Sum.inr v') = 0 := by
  classical
  set n := Nat.card (ClassGroup (𝓞 K))
  set f : ↥(S : Set (HeightOneSpectrum (𝓞 K))) → Multiplicative ℤ :=
    Pi.mulSingle ⟨v.1, v.2⟩ (Multiplicative.ofAdd 1) with hf
  obtain ⟨x, hx⟩ := pow_mem_range_unitValuation (𝓞 K) K (S : Set (HeightOneSpectrum (𝓞 K))) n
    (fun _ ↦ pow_card_eq_one') f
  -- The finite coordinate at `v'` vanishes exactly when the valuation of `x` at `v'` is trivial.
  have hlog (v' : S) :
      logEmbedding S (Additive.ofMul x) (Sum.inr v') = 0 ↔ (f ^ n) ⟨v'.1, v'.2⟩ = 1 := by
    have hpos : 0 < FinitePlace.mk v'.1 ((x : Kˣ) : K) := FinitePlace.pos_iff.mpr (x : Kˣ).ne_zero
    rw [← congrFun hx ⟨v'.1, v'.2⟩, Set.unitValuation_apply,
      HeightOneSpectrum.valuationOfNeZero_eq_one_iff, ← FinitePlace.mk_apply_eq_one_iff,
      logEmbedding_apply_inr]
    exact ⟨Real.eq_one_of_pos_of_log_eq_zero hpos, fun h ↦ by rw [h, Real.log_one]⟩
  refine ⟨x, fun h ↦ ?_, fun v' hv' ↦ (hlog v').mpr ?_⟩
  · rw [hlog, Pi.pow_apply, hf, Pi.mulSingle_eq_same, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_one,
      Nat.cast_eq_zero] at h
    exact Nat.card_pos.ne' h
  · have hne : (⟨v'.1, v'.2⟩ : ↥(S : Set (HeightOneSpectrum (𝓞 K)))) ≠ ⟨v.1, v.2⟩ :=
      fun h ↦ hv' (Subtype.ext (congrArg Subtype.val h))
    rw [Pi.pow_apply, hf, Pi.mulSingle_eq_of_ne hne, one_pow]

/-- The `S`-unit lattice spans the `S`-logarithmic space over `ℝ`. -/
theorem unitLattice_span_eq_top :
    Submodule.span ℝ (unitLattice S : Set (logSpace S)) = ⊤ := by
  classical
  set V := Submodule.span ℝ (unitLattice S : Set (logSpace S))
  -- The inclusion of the ordinary logarithmic space, by zero in the coordinates at `S`.
  let φ : NumberField.Units.dirichletUnitTheorem.logSpace K →ₗ[ℝ] logSpace S :=
    (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).symm.toLinearMap ∘ₗ LinearMap.inl ℝ _ _
  -- The ordinary units fill the infinite coordinates.
  have hφ (y : NumberField.Units.dirichletUnitTheorem.logSpace K) : φ y ∈ V := by
    have hle : Submodule.span ℝ (NumberField.Units.unitLattice K : Set _) ≤ V.comap φ := by
      rw [Submodule.span_le]
      rintro _ ⟨u, -, rfl⟩
      refine Submodule.subset_span ⟨Additive.ofMul
        (unitOfUnits (S : Set (HeightOneSpectrum (𝓞 K))) K u.toMul), ?_⟩
      rw [AddMonoidHom.coe_toIntLinearMap, logEmbedding_unitOfUnits, ofMul_toMul]
      ext i
      cases i <;> simp [φ]
    exact hle (by simp [_root_.NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top K])
  rw [eq_top_iff, ← (Pi.basisFun ℝ _).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply, SetLike.mem_coe]
  cases i with
  | inl w =>
    convert hφ (Pi.single w 1) using 1
    ext j
    cases j <;> simp [φ, Pi.single_apply]
  | inr v =>
    -- An `S`-unit supported at `v`, minus its infinite part, is a multiple of the coordinate
    -- vector at `v`.
    obtain ⟨x, hxv, hxv'⟩ := exists_logEmbedding_inr S v
    set y := logEmbedding S (Additive.ofMul x)
    have hy : y ∈ V := Submodule.subset_span (logEmbedding_mem_unitLattice S _)
    have hdiff : y - φ (fun w ↦ y (Sum.inl w)) = y (Sum.inr v) • Pi.single (Sum.inr v) 1 := by
      ext j
      cases j with
      | inl w => simp [φ]
      | inr v' =>
        by_cases hv' : v' = v
        · subst hv'
          simp [φ]
        · simp [φ, hxv' v' hv', hv']
    have := V.smul_mem (y (Sum.inr v))⁻¹ (V.sub_mem hy (hφ fun w ↦ y (Sum.inl w)))
    rwa [hdiff, smul_smul, inv_mul_cancel₀ hxv, one_smul] at this

open Classical in
/-- The `S`-unit lattice is a full `ℤ`-lattice in the `S`-logarithmic space. -/
instance : IsZLattice ℝ (unitLattice S) where
  span_top := unitLattice_span_eq_top S

open Classical in
/-- The `S`-logarithmic space has dimension `NumberField.Units.rank K + #S`. -/
theorem finrank_logSpace : finrank ℝ (logSpace S) = NumberField.Units.rank K + #S := by
  simp [NumberField.Units.rank]

open Classical in
/-- The `S`-unit lattice has rank `NumberField.Units.rank K + #S`. -/
@[simp]
theorem unitLattice_rank : finrank ℤ (unitLattice S) = NumberField.Units.rank K + #S := by
  rw [ZLattice.rank ℝ, finrank_logSpace]

/-! ### The S-units modulo torsion -/

/-- The kernel of the `S`-logarithmic embedding, as a `ℤ`-linear map, is the torsion submodule of
the `S`-units. -/
theorem ker_logEmbedding_toIntLinearMap :
    LinearMap.ker (logEmbedding S).toIntLinearMap =
      Submodule.torsion ℤ (Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) := by
  ext x
  rw [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap, ← ofMul_toMul x,
    ofMul_mem_torsion_int_iff, logEmbedding_eq_zero_iff]

/-- The `S`-logarithmic embedding induces a `ℤ`-linear equivalence from the `S`-units modulo
torsion onto the `S`-unit lattice. This is the `S`-analogue of Mathlib's
`NumberField.Units.logEmbeddingEquiv`. -/
def logEmbeddingEquiv :
    (Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) ⧸
        Submodule.torsion ℤ (Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))) ≃ₗ[ℤ]
      unitLattice S :=
  (Submodule.quotEquivOfEq _ _ (ker_logEmbedding_toIntLinearMap S).symm).trans
    (logEmbedding S).toIntLinearMap.quotKerEquivRange

/-- The class of an `S`-unit modulo torsion is sent to its `S`-logarithmic image. -/
@[simp]
theorem logEmbeddingEquiv_mk (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    (logEmbeddingEquiv S (Submodule.Quotient.mk x) : logSpace S) = logEmbedding S x :=
  (rfl)

/-- The basis of the `S`-unit lattice formed by the `S`-logarithmic images of the fundamental
system `TauCeti.NumberField.SUnit.fundSystem`. This is the `S`-analogue of Mathlib's
`NumberField.Units.basisUnitLattice`. -/
def basisUnitLattice :
    Basis (Fin (NumberField.Units.rank K + Nat.card (S : Set (HeightOneSpectrum (𝓞 K))))) ℤ
      (unitLattice S) :=
  (basisModTorsion (S : Set (HeightOneSpectrum (𝓞 K)))).map (logEmbeddingEquiv S)

/-- The `S`-logarithmic image of the `i`-th fundamental `S`-unit is the `i`-th vector of
`basisUnitLattice S`. This is the `S`-analogue of Mathlib's
`NumberField.Units.logEmbedding_fundSystem`. -/
theorem logEmbedding_fundSystem
    (i : Fin (NumberField.Units.rank K + Nat.card (S : Set (HeightOneSpectrum (𝓞 K))))) :
    logEmbedding S (Additive.ofMul (fundSystem (S : Set (HeightOneSpectrum (𝓞 K))) i)) =
      basisUnitLattice S i := by
  rw [basisUnitLattice, Basis.map_apply, ← fundSystem_mk, logEmbeddingEquiv_mk]

/-! ### Fundamental systems and bases of the lattice -/

variable {S}

/-- The basis of the `S`-unit lattice formed by the `S`-logarithmic images of a fundamental
system of `S`-units. This is the `S`-analogue of Mathlib's `NumberField.Units.basisOfIsMaxRank`,
with `ℤ` in place of `ℝ`. -/
def basisOfIsFundSystem {ι : Type*} {ε : ι → (S : Set (HeightOneSpectrum (𝓞 K))).unit K}
    (hε : IsFundSystem (S : Set (HeightOneSpectrum (𝓞 K))) ε) :
    Basis ι ℤ (unitLattice S) :=
  (Basis.mk ((isFundSystem_iff ε).mp hε).1 ((isFundSystem_iff ε).mp hε).2.ge).map
    (logEmbeddingEquiv S)

/-- The `i`-th vector of `basisOfIsFundSystem hε` is the `S`-logarithmic image of `ε i`. -/
@[simp]
theorem basisOfIsFundSystem_apply {ι : Type*}
    {ε : ι → (S : Set (HeightOneSpectrum (𝓞 K))).unit K}
    (hε : IsFundSystem (S : Set (HeightOneSpectrum (𝓞 K))) ε) (i : ι) :
    (basisOfIsFundSystem hε i : logSpace S) = logEmbedding S (Additive.ofMul (ε i)) := by
  rw [basisOfIsFundSystem, Basis.map_apply, Basis.mk_apply, logEmbeddingEquiv_mk]

/-- A family of `S`-units is a fundamental system exactly when its `S`-logarithmic images form a
`ℤ`-basis of the `S`-unit lattice. -/
theorem isFundSystem_iff_exists_basis {ι : Type*}
    (ε : ι → (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    IsFundSystem (S : Set (HeightOneSpectrum (𝓞 K))) ε ↔
      ∃ b : Basis ι ℤ (unitLattice S),
        ∀ i, (b i : logSpace S) = logEmbedding S (Additive.ofMul (ε i)) := by
  refine ⟨fun hε ↦ ⟨basisOfIsFundSystem hε, basisOfIsFundSystem_apply hε⟩, ?_⟩
  rintro ⟨b, hb⟩
  have hmk : (fun i ↦ (Submodule.Quotient.mk (Additive.ofMul (ε i)) :
      Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) ⧸
        Submodule.torsion ℤ (Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)))) =
      b.map (logEmbeddingEquiv S).symm := by
    ext1 i
    rw [Basis.map_apply, LinearEquiv.eq_symm_apply, Subtype.ext_iff, logEmbeddingEquiv_mk, hb]
  rw [isFundSystem_iff, hmk]
  exact ⟨Basis.linearIndependent _, Basis.span_eq _⟩

end

end TauCeti.NumberField.SUnit
