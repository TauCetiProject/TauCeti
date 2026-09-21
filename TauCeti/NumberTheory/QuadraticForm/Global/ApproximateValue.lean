/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Representation
public import TauCeti.NumberTheory.NumberField.Global.Approximation.Vector
public import TauCeti.NumberTheory.QuadraticForm.Global.Continuity
public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates

/-!
# Approximating a global value of one summand of an orthogonal sum

Let `U` and `W` be quadratic forms over a number field `K`, with `W` regular. Suppose that `W` is
anisotropic at only finitely many finite places, and that at every finite or real place `v` where
`W_v` is anisotropic there are local vectors `x_v` of `U_v` and `y_v` of `W_v` with
`U(x_v) = -W(y_v) ≠ 0`. Then there is one **global** vector `x` of `U` such that `b := U(x)` is
nonzero and `-b` is represented by `W` at every finite and real place.

The vector `x` is produced by weak approximation of vectors: near each `x_v` the value of `U` stays
in the square class of `U(x_v)`, so `-b` differs from the local value `W(y_v)` by a square. At the
remaining places `W_v` is regular and isotropic, hence universal. The scalar `b` is defined as the
value of the approximating vector; it is not approximated directly. Consequently `b` is represented
by `U` over `K` by construction, which is what makes the argument close up: if `W` satisfies the
local-global principle for the representation of nonzero scalars, then `-b` is represented by `W`
over `K`, and the two global vectors give a nonzero isotropic vector of `U ⊥ W`.

This is the inductive step of the Hasse–Minkowski theorem in rank at least five, where `U` is a
binary summand and `W` its complement of rank at least three.

## Main results

* `QuadraticForm.exists_apply_ne_zero_locallyRepresentsScalar_neg`: a global vector `x` with
  `U x ≠ 0` whose negated value is locally represented by `W`.
* `QuadraticForm.not_anisotropic_prod_of_forall_represents`: if `W` satisfies the local-global
  principle for representing nonzero scalars, then `U ⊥ W` is isotropic over `K`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1973), 66:1, the case of dimension at least
  five.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap
open scoped TensorProduct

namespace TauCeti

variable {K X Y : Type*} [Field K] [NumberField K]
  [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]

/-- Let `W` be a regular quadratic form over a number field that is anisotropic at only finitely
many finite places. If at every finite or real place where `W` is anisotropic some nonzero local
value of `U` is the negative of a local value of `W`, then there is a global vector `x` with
`U x ≠ 0` such that `-U x` is represented by `W` at every finite and real place. -/
theorem _root_.QuadraticForm.exists_apply_ne_zero_locallyRepresentsScalar_neg
    (U : QuadraticForm K X) (W : QuadraticForm K Y) (hU : U ≠ 0) (hW : W.Nondegenerate)
    (hfin : {v : HeightOneSpectrum (𝓞 K) | (W.atFinitePlace v).Anisotropic}.Finite)
    (hfinite : ∀ v, (W.atFinitePlace v).Anisotropic →
      ∃ x y, U.atFinitePlace v x ≠ 0 ∧ U.atFinitePlace v x = -W.atFinitePlace v y)
    (hreal : ∀ w : {w : InfinitePlace K // w.IsReal}, (W.atRealPlace w).Anisotropic →
      ∃ x y, U.atRealPlace w x ≠ 0 ∧ U.atRealPlace w x = -W.atRealPlace w y) :
    ∃ x : X, U x ≠ 0 ∧ W.LocallyRepresentsScalar (-U x) := by
  classical
  -- Equip every localized space of `U` with its module topology.
  let (v : HeightOneSpectrum (𝓞 K)) : TopologicalSpace (v.FiniteScalarExtension (V := X)) :=
    moduleTopology (v.adicCompletion K) _
  have (v : HeightOneSpectrum (𝓞 K)) :
      IsModuleTopology (v.adicCompletion K) (v.FiniteScalarExtension (V := X)) := ⟨rfl⟩
  let (w : {w : InfinitePlace K // w.IsReal}) :
      TopologicalSpace (RealScalarExtension (V := X) w) := moduleTopology ℝ _
  have (w : {w : InfinitePlace K // w.IsReal}) :
      IsModuleTopology ℝ (RealScalarExtension (V := X) w) := ⟨rfl⟩
  -- The exceptional places, the local vectors there, and neighbourhoods preserving square classes.
  let S := hfin.toFinset
  have hrealfin := Set.toFinite
    {w : {w : InfinitePlace K // w.IsReal} | (W.atRealPlace w).Anisotropic}
  let T := hrealfin.toFinset
  choose xS yS hxS hxyS using fun v : S => hfinite v.1 (hfin.mem_toFinset.mp v.2)
  choose xT yT hxT hxyT using fun w : T => hreal w.1 (hrealfin.mem_toFinset.mp w.2)
  choose N hNo hxN hN using fun v : S =>
    U.exists_isOpen_isSquare_div_atFinitePlace v.1 (hxS v)
  choose M hMo hxM hM using fun w : T =>
    U.exists_isOpen_isSquare_div_atRealPlace w.1 (hxT w)
  -- Every global vector whose localizations lie in these neighbourhoods has the required value.
  have hgood (x : X)
      (hxS' : ∀ v : S, ((1 : v.1.adicCompletion K) ⊗ₜ[K] x : v.1.FiniteScalarExtension) ∈ N v)
      (hxT' : ∀ w : T,
        letI : Algebra K ℝ := (embedding_of_isReal w.1.2).toAlgebra
        ((1 : ℝ) ⊗ₜ[K] x : RealScalarExtension w.1) ∈ M w) :
      W.LocallyRepresentsScalar (-U x) := by
    refine (QuadraticForm.locallyRepresentsScalar_iff _ _).mpr ⟨fun v => ?_, fun w => ?_⟩
    · by_cases hvS : v ∈ S
      · obtain ⟨-, hsq⟩ := hN ⟨v, hvS⟩ _ (hxS' ⟨v, hvS⟩)
        have hrep : Represents (W.atFinitePlace v) (-U.atFinitePlace v (xS ⟨v, hvS⟩)) :=
          (represents_iff _ _).mpr ⟨yS ⟨v, hvS⟩, (neg_eq_iff_eq_neg.mpr (hxyS ⟨v, hvS⟩)).symm⟩
        refine hrep.of_isSquare_div (neg_ne_zero.mpr (hxS ⟨v, hvS⟩)) ?_
        simpa [neg_div_neg_eq] using hsq
      · refine represents_of_nondegenerate_of_not_anisotropic _
          (QuadraticForm.Nondegenerate.atFinitePlace hW v) ?_ _
        simpa [S] using hvS
    · let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
      by_cases hwT : w ∈ T
      · obtain ⟨-, hsq⟩ := hM ⟨w, hwT⟩ _ (hxT' ⟨w, hwT⟩)
        have hrep : Represents (W.atRealPlace w) (-U.atRealPlace w (xT ⟨w, hwT⟩)) :=
          (represents_iff _ _).mpr ⟨yT ⟨w, hwT⟩, (neg_eq_iff_eq_neg.mpr (hxyT ⟨w, hwT⟩)).symm⟩
        refine hrep.of_isSquare_div (neg_ne_zero.mpr (hxT ⟨w, hwT⟩)) ?_
        simpa [neg_div_neg_eq] using hsq
      · refine represents_of_nondegenerate_of_not_anisotropic _
          (QuadraticForm.Nondegenerate.atRealPlace hW w) ?_ _
        simpa [T] using hwT
  by_cases hST : S.Nonempty ∨ T.Nonempty
  · -- Some place is exceptional: weak approximation gives `x`, and `U x ≠ 0` is read off there.
    obtain ⟨x, hxS', hxT'⟩ := NumberField.exists_one_tmul_mem_of_mem_nhds S T
      (fun v => (hNo v).mem_nhds (hxN v)) (fun w => (hMo w).mem_nhds (hxM w))
    refine ⟨x, ?_, hgood x hxS' hxT'⟩
    intro hx
    rcases hST with ⟨v, hv⟩ | ⟨w, hw⟩
    · refine (hN ⟨v, hv⟩ _ (hxS' ⟨v, hv⟩)).1 ?_
      simp [hx]
    · refine (hM ⟨w, hw⟩ _ (hxT' ⟨w, hw⟩)).1 ?_
      simp [hx]
  · -- No place is exceptional: any vector with nonzero value works.
    rw [not_or, Finset.not_nonempty_iff_eq_empty, Finset.not_nonempty_iff_eq_empty] at hST
    obtain ⟨x, hx⟩ : ∃ x, U x ≠ 0 := by
      by_contra! h
      exact hU (QuadraticMap.ext h)
    refine ⟨x, hx, hgood x (fun v => ?_) (fun w => ?_)⟩
    · exact absurd v.2 (by simp [hST.1])
    · exact absurd w.2 (by simp [hST.2])

/-- Let `W` be a regular quadratic form over a number field that is anisotropic at only finitely
many finite places, and suppose that at every finite or real place where `W` is anisotropic some
nonzero local value of `U` is the negative of a local value of `W`. If `W` represents over `K`
every nonzero scalar that it represents at every finite and real place, then the orthogonal sum
`U ⊥ W` is isotropic over `K`. -/
theorem _root_.QuadraticForm.not_anisotropic_prod_of_forall_represents
    (U : QuadraticForm K X) (W : QuadraticForm K Y) (hU : U ≠ 0) (hW : W.Nondegenerate)
    (hfin : {v : HeightOneSpectrum (𝓞 K) | (W.atFinitePlace v).Anisotropic}.Finite)
    (hfinite : ∀ v, (W.atFinitePlace v).Anisotropic →
      ∃ x y, U.atFinitePlace v x ≠ 0 ∧ U.atFinitePlace v x = -W.atFinitePlace v y)
    (hreal : ∀ w : {w : InfinitePlace K // w.IsReal}, (W.atRealPlace w).Anisotropic →
      ∃ x y, U.atRealPlace w x ≠ 0 ∧ U.atRealPlace w x = -W.atRealPlace w y)
    (hlocal : ∀ b : K, b ≠ 0 → W.LocallyRepresentsScalar b → Represents W b) :
    ¬ (U.prod W).Anisotropic := by
  obtain ⟨x, hx, hloc⟩ :=
    U.exists_apply_ne_zero_locallyRepresentsScalar_neg W hU hW hfin hfinite hreal
  obtain ⟨y, hy⟩ := (represents_iff _ _).mp (hlocal _ (neg_ne_zero.mpr hx) hloc)
  intro hanis
  have hxy := hanis (x, y) (by rw [QuadraticMap.prod_apply, hy, add_neg_cancel])
  rw [Prod.mk_eq_zero] at hxy
  exact hx (by rw [hxy.1, map_zero])

end TauCeti
