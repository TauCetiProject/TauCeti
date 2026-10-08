/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Supersingular
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Verschiebung
-- Proof-only: separability is invariant under base change.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
-- Proof-only: `deg [n] = n ²`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
-- Proof-only: `[p]` and relative Frobenius under base change.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Naturality
-- Proof-only: embeddings agreeing on `[p]^* F(W)` differ by `p`-torsion at the generic point.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard

/-!
# Supersingularity and the Verschiebung

Let `W` be an elliptic curve over a field `K` of exponential characteristic `p`. This file proves
that `W` is supersingular — it has no nonzero geometric point of order `p` — exactly when
multiplication by `p` is purely inseparable (has separable degree `1`), and exactly when the
Verschiebung `V : W⁽ᵖ⁾ → W` is purely inseparable (Silverman V.3.1). The definition of
supersingularity reads the `p`-torsion over an algebraic closure; the criterion reads only the
function fields over `K`, so it makes no choice of closure and holds verbatim over imperfect and
transcendental base fields.

Both implications go through the separable degree of `[p]`.

* If the geometric `p`-torsion is trivial, `[p]` is purely inseparable. Two `K`-embeddings of
  `K(W)` into an algebraic closure `Ω` of `K(W)` that agree on `[p]^* K(W)` move the generic point
  by a `p`-torsion point of `W(Ω)` (`TauCeti.Isogeny.zsmul_map_sub_map_genericPoint_eq_zero`).
  That point is zero, and an embedding is determined by the image of the generic point, so there
  is only one embedding: the separable degree of `[p]` is `1`.
* If `V` is purely inseparable, the geometric `p`-torsion is trivial. Base change along
  `K → Kᵃˡᵍ` carries `V ∘ F_{W/K} = [p]` to a factorisation of `[p]` of `W` over `Kᵃˡᵍ`. The base
  change of relative Frobenius is purely inseparable of degree `p`, so that of `V` has degree `p`
  as well; it is not separable, since separability is invariant under base change, so it is
  purely inseparable. Hence `[p]` over `Kᵃˡᵍ` has separable degree `1`, so it has no kernel, and
  its kernel is the geometric `p`-torsion.

Since `[p] = V ∘ F_{W/K}` with `F_{W/K}` purely inseparable, `[p]` and `V` have the same
separable degree, which connects the two.

## Main results

* `WeierstrassCurve.isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one`: `W` is
  supersingular exactly when `[p]` has separable degree `1`.
* `WeierstrassCurve.isSupersingular_iff_isPurelyInseparable_verschiebungIsogeny`: `W` is
  supersingular exactly when its Verschiebung is purely inseparable.
* `WeierstrassCurve.isOrdinary_iff_isSeparable_verschiebungIsogeny`: in characteristic `p > 0`,
  `W` is ordinary exactly when its Verschiebung is separable.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.1 and V.3.1.
-/

public section

open TauCeti.Isogeny WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {K : Type*} [Field K] (p : ℕ) [ExpChar K p] (W : WeierstrassCurve K) [W.IsElliptic]

/-- In characteristic `p > 0` the Verschiebung, of prime degree `p`, is not both separable and of
separable degree `1`. -/
private theorem not_isSeparable_verschiebungIsogeny_of_separableDegree_eq_one (hp : p.Prime)
    (hV : (verschiebungIsogeny p W.toAffine).separableDegree = 1) :
    ¬Algebra.IsSeparable (verschiebungIsogeny p W.toAffine).fieldPullback.fieldRange
      (W.map (frobenius K p)).toAffine.FunctionField := fun _ ↦ by
  have h := (verschiebungIsogeny p W.toAffine).separableDegree_mul_inseparableDegree
  rw [hV, inseparableDegree_eq_one_of_isSeparable, degree_verschiebungIsogeny] at h
  exact hp.one_lt.ne h

open scoped Classical in
/-- On a supersingular curve `[p]` has separable degree `1`. -/
private theorem separableDegree_mulByIntIsogenyOfNeZero_eq_one_of_isSupersingular
    (hW : W.IsSupersingular p) :
    (mulByIntIsogenyOfNeZero W.toAffine (n := p)
      (mod_cast expChar_ne_zero K p)).separableDegree = 1 := by
  set φ := mulByIntIsogenyOfNeZero W.toAffine (n := p) (mod_cast expChar_ne_zero K p)
  set Ω := AlgebraicClosure W.toAffine.FunctionField
  have htors := (W.isSupersingular_iff_of_isAlgClosed (expChar_ne_zero K p) Ω).1 hW
  -- Two embeddings over `[p]^* K(W)` move the generic point by a `p`-torsion point, which is zero.
  have : Subsingleton (Field.Emb φ.fieldPullback.fieldRange W.toAffine.FunctionField) := by
    refine ⟨fun σ τ ↦ AlgHom.restrictScalars_injective K
      (map_genericPoint_injective W.toAffine ?_)⟩
    have hdiff := zsmul_map_sub_map_genericPoint_eq_zero W.toAffine _ (σ.restrictScalars K)
      (τ.restrictScalars K) fun z hz ↦ by
        simpa using (σ.commutes ⟨z, hz⟩).trans (τ.commutes ⟨z, hz⟩).symm
    have hmem : Point.map (σ.restrictScalars K) (genericPoint W.toAffine) -
        Point.map (τ.restrictScalars K) (genericPoint W.toAffine) ∈
          AddSubgroup.torsionBy (W.baseChange Ω).toAffine.Point p :=
      AddSubgroup.torsionBy.nsmul_iff.2 (by exact_mod_cast hdiff)
    rw [htors, AddSubgroup.mem_bot, sub_eq_zero] at hmem
    exact hmem
  rw [separableDegree_def, Field.finSepDegree]
  exact Nat.card_eq_one_iff_unique.2 ⟨this, inferInstance⟩

open scoped Classical in
/-- A curve whose Verschiebung has separable degree `1` is supersingular. -/
private theorem isSupersingular_of_separableDegree_verschiebungIsogeny_eq_one
    (hV : (verschiebungIsogeny p W.toAffine).separableDegree = 1) : W.IsSupersingular p := by
  set ι := algebraMap K (AlgebraicClosure K)
  set V := verschiebungIsogeny p W.toAffine
  set Fr := relativeFrobeniusIsogeny p W.toAffine
  have hp : (p : ℤ) ≠ 0 := mod_cast expChar_ne_zero K p
  -- Base change carries `V ∘ F_{W/K} = [p]` to `[p]` over the algebraic closure.
  have hcomp : (V.map ι).comp (Fr.map ι) = mulByIntIsogenyOfNeZero (W.map ι) hp := by
    rw [← TauCeti.Isogeny.comp_map, verschiebungIsogeny_comp_relativeFrobeniusIsogeny,
      mulByIntIsogeny_map]
  -- The base change of `V` has degree `p`, by the tower formula against `deg [p] = p ²`.
  have hdeg : (V.map ι).degree = p := by
    have h := congrArg TauCeti.Isogeny.degree hcomp
    rw [degree_comp, degree_relativeFrobeniusIsogeny_map, degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast, sq] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (expChar_ne_zero K p)) h
  -- It is purely inseparable: if it were separable then so would `V` be, of degree `p` and
  -- separable degree `1`.
  have hsep : (V.map ι).separableDegree = 1 := by
    have hdvd := Dvd.intro _ (V.map ι).separableDegree_mul_inseparableDegree
    rw [hdeg] at hdvd
    rcases ‹ExpChar K p› with _ | ⟨hprime⟩
    · exact Nat.dvd_one.1 hdvd
    refine (hprime.eq_one_or_self_of_dvd _ hdvd).resolve_right fun hsp ↦ ?_
    have hins : (V.map ι).inseparableDegree = 1 := by
      have h := (V.map ι).separableDegree_mul_inseparableDegree
      rw [hsp, hdeg] at h
      exact (Nat.mul_eq_left hprime.ne_zero).1 h
    exact not_isSeparable_verschiebungIsogeny_of_separableDegree_eq_one p W hprime hV
      ((isSeparable_map_iff V ι).1 ((V.map ι).inseparableDegree_eq_one_iff_isSeparable.1 hins))
  -- So `[p]` over the algebraic closure has trivial kernel.
  have hker : (mulByIntIsogenyOfNeZero (W.map ι) hp).ker = ⊥ := by
    refine ker_eq_bot_of_separableDegree_eq_one ?_
    rw [← hcomp, separableDegree_comp, hsep, separableDegree_relativeFrobeniusIsogeny_map]
  -- That kernel is the `p`-torsion of `W` over the algebraic closure.
  rw [ker_mulByIntIsogeny_eq_torsionBy, Affine.baseChange_self] at hker
  exact (W.isSupersingular_iff_of_isAlgClosed (expChar_ne_zero K p) (AlgebraicClosure K)).2 hker

/-- **Supersingularity is pure inseparability of `[p]`**: `W` is supersingular exactly when
multiplication by `p` has separable degree `1` (Silverman V.3.1). -/
theorem isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one :
    W.IsSupersingular p ↔ (mulByIntIsogenyOfNeZero W.toAffine (n := p)
      (mod_cast expChar_ne_zero K p)).separableDegree = 1 := by
  refine ⟨separableDegree_mulByIntIsogenyOfNeZero_eq_one_of_isSupersingular p W, fun h ↦ ?_⟩
  exact isSupersingular_of_separableDegree_verschiebungIsogeny_eq_one p W
    ((separableDegree_verschiebungIsogeny p W.toAffine).trans h)

/-- **Supersingularity is pure inseparability of the Verschiebung**: `W` is supersingular exactly
when `V : W⁽ᵖ⁾ → W`, the dual of relative Frobenius, is purely inseparable (Silverman V.3.1). -/
theorem isSupersingular_iff_isPurelyInseparable_verschiebungIsogeny :
    W.IsSupersingular p ↔ IsPurelyInseparable
      (verschiebungIsogeny p W.toAffine).fieldPullback.fieldRange
      (W.map (frobenius K p)).toAffine.FunctionField := by
  rw [← separableDegree_eq_one_iff_isPurelyInseparable, separableDegree_verschiebungIsogeny,
    isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one]

/-- **Ordinarity is separability of the Verschiebung**: in characteristic `p > 0`, `W` is ordinary
exactly when `V : W⁽ᵖ⁾ → W` is separable. The Verschiebung has prime degree `p`, so it is
separable or purely inseparable and not both. In characteristic zero (`p = 1`) every curve is
supersingular in this sense and `V` is an isomorphism, so the statement needs `p` prime. -/
theorem isOrdinary_iff_isSeparable_verschiebungIsogeny (hp : p.Prime) :
    W.IsOrdinary p ↔ Algebra.IsSeparable
      (verschiebungIsogeny p W.toAffine).fieldPullback.fieldRange
      (W.map (frobenius K p)).toAffine.FunctionField := by
  rw [← not_isSupersingular, isSupersingular_iff_isPurelyInseparable_verschiebungIsogeny]
  exact ⟨(isSeparable_or_isPurelyInseparable_verschiebungIsogeny p W.toAffine).resolve_right,
    fun hsep hpi ↦ not_isSeparable_verschiebungIsogeny_of_separableDegree_eq_one p W hp
      ((separableDegree_eq_one_iff_isPurelyInseparable _).2 hpi) hsep⟩

end WeierstrassCurve

end
