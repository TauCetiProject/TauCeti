/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Basic
public import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry

/-!
# The differentiated Cauchy–Riemann system with Sobolev coefficients

Write `z = s + i t` on `ℂ` and consider the operator `ξ ↦ ∂_s ξ + J ∂_t ξ + S ξ` for coefficient
fields `J, S : ℂ → (V →L[ℝ] V)` on a finite-dimensional real normed space `V`, where, for a weak
derivative `Dξ` of `ξ`, `∂_s ξ = Dξ(·) 1` and `∂_t ξ = Dξ(·) I`. Interior regularity for this
operator is proved by induction on the order (McDuff–Salamon, Proposition B.4.9, Steps 2 and 3):
the pair `Ξ = (∂_s ξ, ∂_t ξ)` solves a system of the same shape,

`∂_s Ξ + J₂ ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)`,

with `J₂ = diag(J, J)` and `S₂ = [[S, ∂_s J], [0, S + ∂_t J]]`. The classical computation for
`C²` maps is `TauCeti.crOperator_differentiated_system`. This file proves the strong form for
Sobolev data: for `p > 2`, `1 < q ≤ p`, `J, S ∈ W^{1,p}_loc`, `ξ ∈ W^{2,q}_loc` and
`η ∈ W^{1,q}_loc` with `∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on an open `Ω`, the pair `Ξ`
is in `W^{1,q}_loc` and every weak derivative of `Ξ` satisfies the differentiated system almost
everywhere on `Ω`. The products `J ∂_t ξ` and `S ξ` are differentiated by the weak Leibniz rule
for mixed exponents, and the mixed second weak derivatives of `ξ` commute.
Regularity of `ξ` beyond `W^{2,q}_loc` is not needed for the identity, so this covers every
order `k ≥ 2` of the induction.

The coefficients of the new system inherit the regularity the induction needs: `J₂` has the
regularity of `J`, and `S₂` is in `W^{k,p}_loc` as soon as `S ∈ W^{k,p}_loc` and
`J ∈ W^{k+1,p}_loc`. The right side is locally `L^q`. Its higher regularity is a question about
mixed-exponent products of higher order and is not addressed here.

## Main declarations

* `TauCeti.MemWkpLoc.memWkpLoc_partials_of_hasWeakFDerivOn`: `Ξ = (∂_s ξ, ∂_t ξ) ∈ W^{k,q}_loc`
  for `ξ ∈ W^{k+1,q}_loc`.
* `TauCeti.ae_differentiated_cauchyRiemann`: the differentiated system, almost everywhere.
* `TauCeti.MemWkpLoc.differentiatedCRCoefficient`: the regularity of `S₂`.
* `TauCeti.memLpLoc_differentiatedCR_rightSide`: the right side is locally `L^q`.
* `TauCeti.ae_differentiated_cauchyRiemann_const`: for a constant coefficient `J` and `S = 0`,
  the system is the original operator applied to each component of `Ξ`.

The coefficient `S₂` is `TauCeti.differentiatedCRCoefficient`, and
`TauCeti.differentiatedCRCoefficient_ne_prodMap` shows `S₂ ≠ diag(S, S)` as soon as `∂_s J ≠ 0`.
The regularity of `J₂` is `TauCeti.MemWkpLoc.prodMap`, and `J₂² = -1` whenever `J² = -1` is
`TauCeti.prodMap_mul_self_eq_neg_one`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.4.9.
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable [FiniteDimensional ℝ V] {Ω : Opens ℂ} {k : ℕ}

/-- **The partial derivatives of a `W^{k+1,q}_loc` map.** For a weak derivative `Dξ` of
`ξ ∈ W^{k+1,q}_loc`, the pair `Ξ = (∂_s ξ, ∂_t ξ) = (Dξ(·) 1, Dξ(·) I)` is in `W^{k,q}_loc`. -/
theorem MemWkpLoc.memWkpLoc_partials_of_hasWeakFDerivOn {q : ℝ≥0∞} {ξ : ℂ → V}
    {Dξ : ℂ → ℂ →L[ℝ] V} (hξ : MemWkpLoc q Ω (k + 1) ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ) :
    MemWkpLoc q Ω k (fun z => (Dξ z 1, Dξ z I)) := by
  have h := hξ.memWkpLoc_of_hasWeakFDerivOn hDξ
  exact (h.clm_comp (ContinuousLinearMap.apply ℝ V 1)).prodMk
    (h.clm_comp (ContinuousLinearMap.apply ℝ V I))

/-- **The differentiated system.** Let `p > 2` and `1 < q ≤ p`. Let `J, S ∈ W^{1,p}_loc(Ω)` have
weak derivatives `DJ`, `DS`, let `ξ ∈ W^{2,q}_loc(Ω)` have weak derivative `Dξ`, and let `η` have
weak derivative `Dη`. If `∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on `Ω`, then every weak
derivative `DΞ` of `Ξ = (∂_s ξ, ∂_t ξ)` satisfies, almost everywhere on `Ω`,
`∂_s Ξ + J₂ ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)`,
with `J₂ = diag(J, J)` and `S₂ = TauCeti.differentiatedCRCoefficient S DJ`.
Such a `DΞ` exists by `TauCeti.MemWkpLoc.memWkpLoc_partials_of_hasWeakFDerivOn`. -/
theorem ae_differentiated_cauchyRiemann {p q : ℝ≥0} (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    {Dξ Dη : ℂ → ℂ →L[ℝ] V} {DΞ : ℂ → ℂ →L[ℝ] V × V}
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 2 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    (hDΞ : HasWeakFDerivOn volume Ω (fun z => (Dξ z 1, Dξ z I)) DΞ) :
    ∀ᵐ z ∂volume.restrict Ω, DΞ z 1 + (J z).prodMap (J z) (DΞ z I) +
        differentiatedCRCoefficient (S z) (DJ z) (Dξ z 1, Dξ z I) =
      (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z)) := by
  have : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le.trans hqp⟩
  have hDξ1 : MemWkpLoc q Ω 1 Dξ := hξ.memWkpLoc_of_hasWeakFDerivOn hDξ
  obtain ⟨D2, hD2, hD2q⟩ := hDξ1.exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hD2q
  -- The partial derivatives `z ↦ Dξ z v` have weak derivatives `w ↦ D2 z w v`.
  have hpart (v : ℂ) : HasWeakFDerivOn volume Ω (fun z => Dξ z v)
      (fun z => (ContinuousLinearMap.apply ℝ V v).comp (D2 z)) :=
    hD2.clm_comp (ContinuousLinearMap.apply ℝ V v)
  have hpartLp (v : ℂ) : MemLpLoc q Ω (fun z => Dξ z v) :=
    hDξ1.memLpLoc.clm_comp (ContinuousLinearMap.apply ℝ V v)
  have hpartDLp (v : ℂ) :
      MemLpLoc q Ω (fun z => (ContinuousLinearMap.apply ℝ V v).comp (D2 z)) :=
    hD2q.clm_comp (ContinuousLinearMap.compL ℝ ℂ (ℂ →L[ℝ] V) V (ContinuousLinearMap.apply ℝ V v))
  -- The mixed second weak derivatives of `ξ` commute.
  have hsymm : (fun z => D2 z I 1) =ᵐ[volume.restrict Ω] fun z => D2 z 1 I :=
    ((hDξ.hasWeakLineDerivOn 1).comm ((hpart 1).hasWeakLineDerivOn I)
      (hDξ.hasWeakLineDerivOn I)).ae_eq ((hpart I).hasWeakLineDerivOn 1)
  -- The weak Leibniz rule for `J ∂_t ξ` and `S ξ`.
  have hJξ := hDJ.bilin_of_memLpLoc (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq hqp
    ((hJ.memLpLoc_of_holderTriple hp le_rfl).mono_exponent le_top)
    (hJ.memLpLoc_of_hasWeakFDerivOn hDJ) (hpart I) (hpartLp I) (hpartDLp I)
  have hSξ := hDS.bilin_of_memLpLoc (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq hqp
    ((hS.memLpLoc_of_holderTriple hp le_rfl).mono_exponent le_top)
    (hS.memLpLoc_of_hasWeakFDerivOn hDS) hDξ hξ.memLpLoc hDξ1.memLpLoc
  -- Differentiating the equation.
  have hsum := (((hpart 1).add hJξ).add hSξ).congr_ae (heq.mono fun z hz => by simpa using hz)
  have hη := hsum.ae_eq hDη
  have hΞ := hDΞ.ae_eq ((hpart 1).prodMk (hpart I))
  filter_upwards [hη, hΞ, hsymm] with z h1 h2 h3
  -- The `∂_s` and `∂_t` components of the differentiated equation.
  have e1 : D2 z 1 1 + (DJ z 1 (Dξ z I) + J z (D2 z 1 I)) + (DS z 1 (ξ z) + S z (Dξ z 1)) =
      Dη z 1 := by
    simpa using congr($h1 1)
  have eI : D2 z I 1 + (DJ z I (Dξ z I) + J z (D2 z I I)) + (DS z I (ξ z) + S z (Dξ z I)) =
      Dη z I := by
    simpa using congr($h1 I)
  rw [h2]
  ext
  · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply,
      Prod.mk_add_mk, differentiatedCRCoefficient_apply, h3]
    rw [← e1]
    abel
  · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply,
      Prod.mk_add_mk, differentiatedCRCoefficient_apply, ← h3]
    rw [← eI]
    abel

/-- **Regularity of `S₂`.** If `S ∈ W^{k,p}_loc(Ω)` and `J ∈ W^{k+1,p}_loc(Ω)` with weak
derivative `DJ`, then `S₂ = [[S, ∂_s J], [0, S + ∂_t J]]` is in `W^{k,p}_loc(Ω)`. For
`S ∈ W^{m,p}_loc` and `J ∈ W^{ℓ,p}_loc` this gives `S₂ ∈ W^{min(m, ℓ - 1),p}_loc` after lowering the
orders with `TauCeti.MemWkpLoc.of_le`. -/
theorem MemWkpLoc.differentiatedCRCoefficient {p : ℝ≥0∞} {J S : ℂ → V →L[ℝ] V}
    {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} (hS : MemWkpLoc p Ω k S) (hJ : MemWkpLoc p Ω (k + 1) J)
    (hDJ : HasWeakFDerivOn volume Ω J DJ) :
    MemWkpLoc p Ω k (fun z => TauCeti.differentiatedCRCoefficient (S z) (DJ z)) := by
  simpa using (hS.prodMk (hJ.memWkpLoc_of_hasWeakFDerivOn hDJ)).clm_comp
    differentiatedCRCoefficientL

/-- **The right side of the differentiated system is locally `L^q`.** For `p > 2`, `1 ≤ q ≤ p`,
`S ∈ W^{1,p}_loc(Ω)` with weak derivative `DS` and `ξ, η ∈ W^{1,q}_loc(Ω)` with `η` having weak
derivative `Dη`, the map `(∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` is in `L^q_loc(Ω)`. -/
theorem memLpLoc_differentiatedCR_rightSide {p q : ℝ≥0} (hp : 2 < p) (hq : 1 ≤ q) (hqp : q ≤ p)
    {S : ℂ → V →L[ℝ] V} {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V} {Dη : ℂ → ℂ →L[ℝ] V}
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS) (hξ : MemWkpLoc q Ω 1 ξ)
    (hη : MemWkpLoc q Ω 1 η) (hDη : HasWeakFDerivOn volume Ω η Dη) :
    MemLpLoc q Ω (fun z => (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
  have hDSp := hS.memLpLoc_of_hasWeakFDerivOn hDS
  have hDηq := hη.memLpLoc_of_hasWeakFDerivOn hDη
  have hcomp (v : ℂ) : MemLpLoc q Ω (fun z => Dη z v - DS z v (ξ z)) :=
    (hDηq.clm_comp (ContinuousLinearMap.apply ℝ V v)).sub
      (MemLpLoc.bilin_of_memWkpLoc (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hqp
        (hDSp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)) hξ)
  exact memWkpLoc_zero_iff.1
    ((memWkpLoc_zero_iff.2 (hcomp 1)).prodMk (memWkpLoc_zero_iff.2 (hcomp I)))

/-- **Check: the constant case.** For a constant structure `J = A` and `S = 0`, the differentiated
system is the original operator `∂_s + A ∂_t` applied to each component of `Ξ = (∂_s ξ, ∂_t ξ)`:
every weak derivative `DΞ` of `Ξ` satisfies `∂_s Ξ + diag(A, A) ∂_t Ξ = (∂_s η, ∂_t η)` almost
everywhere on `Ω`. -/
theorem ae_differentiated_cauchyRiemann_const {q : ℝ≥0} (hq : 1 < q) (A : V →L[ℝ] V)
    {ξ η : ℂ → V} {Dξ Dη : ℂ → ℂ →L[ℝ] V} {DΞ : ℂ → ℂ →L[ℝ] V × V}
    (hξ : MemWkpLoc q Ω 2 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + A (Dξ z I) = η z)
    (hDΞ : HasWeakFDerivOn volume Ω (fun z => (Dξ z 1, Dξ z I)) DΞ) :
    ∀ᵐ z ∂volume.restrict Ω, DΞ z 1 + A.prodMap A (DΞ z I) = (Dη z 1, Dη z I) := by
  have hA : HasWeakFDerivOn volume Ω (fun _ => A) 0 := hasWeakFDerivOn_iff.2 fun v => by
    simpa using hasWeakLineDerivOn_const (μ := volume) (Ω := Ω) (v := v) A
  have h0 : HasWeakFDerivOn volume Ω (0 : ℂ → V →L[ℝ] V) 0 := hasWeakFDerivOn_zero
  have h := ae_differentiated_cauchyRiemann (p := max q 3) (lt_max_of_lt_right (by norm_num)) hq
    (le_max_left _ _) (memWkpLoc_const A) hA memWkpLoc_zero_fun h0 hξ hDξ hDη
    (heq.mono fun z hz => by simpa using hz) hDΞ
  filter_upwards [h] with z hz
  simpa using hz

end TauCeti
