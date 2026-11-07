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

/-- Over a field, a regular quadratic form `Q` represents `-c` as soon as, if `Q` is anisotropic,
`c` lies in the square class of some nonzero `c₀` that is the negative of a value of `Q`. -/
private theorem represents_neg_of_forall_anisotropic {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] (Q : QuadraticForm F V) (hQ : Q.Nondegenerate) (c : F)
    (h : Q.Anisotropic → ∃ c₀ y, c₀ ≠ 0 ∧ c₀ = -Q y ∧ IsSquare (c / c₀)) :
    Represents Q (-c) := by
  by_cases han : Q.Anisotropic
  · obtain ⟨c₀, y, hc₀, hxy, hsq⟩ := h han
    have hrep : Represents Q (-c₀) :=
      (represents_iff _ _).mpr ⟨y, (neg_eq_iff_eq_neg.mpr hxy).symm⟩
    refine hrep.of_isSquare_div (neg_ne_zero.mpr hc₀) ?_
    simpa [neg_div_neg_eq] using hsq
  · exact represents_of_nondegenerate_of_not_anisotropic _ hQ han _

omit [FiniteDimensional K X] in
/-- If `W` is regular, then `-U x` is represented at a finite place `v` as soon as, where `W_v` is
anisotropic, the value `U_v (1 ⊗ x)` lies in the square class of a local value of `U_v` that is
the negative of a local value of `W_v`. -/
private theorem represents_atFinitePlace_neg_apply
    (U : QuadraticForm K X) (W : QuadraticForm K Y) (hW : W.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 K)) (x : X)
    (h : (W.atFinitePlace v).Anisotropic →
      ∃ x₀ y, U.atFinitePlace v x₀ ≠ 0 ∧ U.atFinitePlace v x₀ = -W.atFinitePlace v y ∧
        IsSquare (U.atFinitePlace v ((1 : v.adicCompletion K) ⊗ₜ[K] x) / U.atFinitePlace v x₀)) :
    Represents (W.atFinitePlace v) (algebraMap K (v.adicCompletion K) (-U x)) := by
  simpa using represents_neg_of_forall_anisotropic _
    (QuadraticForm.Nondegenerate.atFinitePlace hW v)
    (U.atFinitePlace v ((1 : v.adicCompletion K) ⊗ₜ[K] x)) fun han => by
      obtain ⟨x₀, y, hx₀, hxy, hsq⟩ := h han
      exact ⟨_, y, hx₀, hxy, hsq⟩

omit [FiniteDimensional K X] in
/-- If `W` is regular, then `-U x` is represented at a real place `w` as soon as, where `W_w` is
anisotropic, the value `U_w (1 ⊗ x)` lies in the square class of a local value of `U_w` that is
the negative of a local value of `W_w`. -/
private theorem represents_atRealPlace_neg_apply
    (U : QuadraticForm K X) (W : QuadraticForm K Y) (hW : W.Nondegenerate)
    (w : {w : InfinitePlace K // w.IsReal}) (x : X)
    (h : (W.atRealPlace w).Anisotropic →
      ∃ x₀ y, U.atRealPlace w x₀ ≠ 0 ∧ U.atRealPlace w x₀ = -W.atRealPlace w y ∧
        letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
        IsSquare (U.atRealPlace w ((1 : ℝ) ⊗ₜ[K] x : RealScalarExtension w) / U.atRealPlace w x₀)) :
    Represents (W.atRealPlace w) (embedding_of_isReal w.2 (-U x)) := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  simpa using represents_neg_of_forall_anisotropic _
    (QuadraticForm.Nondegenerate.atRealPlace hW w)
    (U.atRealPlace w ((1 : ℝ) ⊗ₜ[K] x : RealScalarExtension w)) fun han => by
      obtain ⟨x₀, y, hx₀, hxy, hsq⟩ := h han
      exact ⟨_, y, hx₀, hxy, hsq⟩

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
    · refine represents_atFinitePlace_neg_apply U W hW v x fun han => ?_
      have hvS : v ∈ S := by simpa [S] using han
      exact ⟨xS ⟨v, hvS⟩, yS ⟨v, hvS⟩, hxS ⟨v, hvS⟩, hxyS ⟨v, hvS⟩,
        (hN ⟨v, hvS⟩ _ (hxS' ⟨v, hvS⟩)).2⟩
    · refine represents_atRealPlace_neg_apply U W hW w x fun han => ?_
      have hwT : w ∈ T := by simpa [T] using han
      exact ⟨xT ⟨w, hwT⟩, yT ⟨w, hwT⟩, hxT ⟨w, hwT⟩, hxyT ⟨w, hwT⟩,
        (hM ⟨w, hwT⟩ _ (hxT' ⟨w, hwT⟩)).2⟩
  by_cases hST : S.Nonempty ∨ T.Nonempty
  · -- Some place is exceptional: weak approximation gives `x`, and `U x ≠ 0` is read off there.
    obtain ⟨x, hxS', hxT'⟩ := NumberField.exists_one_tmul_mem_of_mem_nhds S T
      (fun v => (hNo v).mem_nhds (hxN v)) (fun w => (hMo w).mem_nhds (hxM w))
    refine ⟨x, ?_, hgood x hxS' hxT'⟩
    intro hx
    rcases hST with ⟨v, hv⟩ | ⟨w, hw⟩
    · exact (hN ⟨v, hv⟩ _ (hxS' ⟨v, hv⟩)).1 (by simp [hx])
    · exact (hM ⟨w, hw⟩ _ (hxT' ⟨w, hw⟩)).1 (by simp [hx])
  · -- No place is exceptional: any vector with nonzero value works.
    rw [not_or, Finset.not_nonempty_iff_eq_empty, Finset.not_nonempty_iff_eq_empty] at hST
    obtain ⟨x, hx⟩ : ∃ x, U x ≠ 0 := by
      by_contra! h; exact hU (QuadraticMap.ext h)
    exact ⟨x, hx, hgood x (fun v => absurd v.2 (by simp [hST.1]))
      (fun w => absurd w.2 (by simp [hST.2]))⟩

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
