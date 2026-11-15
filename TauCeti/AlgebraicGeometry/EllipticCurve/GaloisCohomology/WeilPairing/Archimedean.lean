/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Orthogonality
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Archimedean.Duality
import TauCeti.Algebra.Module.Torsion.Int
import TauCeti.Algebra.Module.ZMod.Annihilator
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Real
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapEquiv
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Cardinality
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Local
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard
import TauCeti.GroupTheory.Index.NSmul

/-!
# Archimedean local Tate duality for elliptic torsion and isogeny kernels

For an elliptic curve `E` over `ℝ` or `K_w` (`w` an infinite place) and `m ≠ 0`, cup product along
the Weil pairing followed by `realH2MuToZMod` / `infiniteH2MuToZMod` gives a perfect pairing
`H¹(G, E[m]) × H¹(G, E[m]) → ZMod m` (`WeierstrassCurve.realTateWeilPairing`,
`WeierstrassCurve.infiniteTateWeilPairing`). For an isogeny `φ : E₁ → E₂` with dual `φ̂`, cup
product along `e_φ` gives a perfect pairing `H¹(G, E₁[φ]) × H¹(G, E₂[φ̂]) → ZMod (deg φ)`
(`TauCeti.Isogeny.realTateKerWeilPairing`, `TauCeti.Isogeny.infiniteTateKerWeilPairing`).

Combining perfection with archimedean Euler characteristic (`Brauer.Archimedean.Duality`), real
period index formulas (`Affine.Point.Index.Real`), and Kummer orthogonality yields at every `w`:
* `m ^ (2 * w.mult) · #H¹(K_w, E[m]) = #E(K_w)[m]²`, `#H¹_m(K_w)² = #H¹(K_w, E[m])`, and exact
  self-orthogonality of the local Selmer condition / Kummer image under `infiniteTateWeilPairing`;
* `(deg φ) ^ w.mult · #H¹(K_w, E₁[φ]) = #E₁(K_w)[φ] · #E₂(K_w)[φ̂]`, `#H¹_φ(K_w) · #H¹_φ̂(K_w) =
  #H¹(K_w, E₁[φ])`, and exact mutual orthogonality of the local Selmer / Kummer subgroups.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, Theorem 2.13 and Proposition 3.8.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII*, J. reine angew. Math. 217 (1965).
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory NumberField NumberField.InfinitePlace

private theorem finite_galois_completion {K : Type*} [Field K] (w : InfinitePlace K) :
    Finite (AbsoluteGaloisGroup w.Completion) :=
  w.isReal_or_isComplex.elim
    (fun hw => Nat.finite_of_card_ne_zero (by
      rw [natCard_absoluteGaloisGroup_of_isReal w hw]; decide))
    fun hw => @Finite.of_subsingleton _
      (Completion.ringEquivComplexOfIsComplex hw).absoluteGaloisGroupCongr.symm.toEquiv.subsingleton

private theorem unit_natCast {F : Type*} [Field F] [CharZero F] (n : ℕ) [NeZero n] :
    IsUnit (n : F) :=
  (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit

namespace WeierstrassCurve

section AbstractField

local notation "Gal" => AbsoluteGaloisGroup

variable {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]

private theorem mul_index_range_nsmul_eq_natCard_torsionBy_of_ringEquivReal [DecidableEq F]
    (e : F ≃+* ℝ) {m : ℕ} (hm : m ≠ 0) :
    m * (nsmulAddMonoidHom (α := W.toAffine.Point) m).range.index =
      Nat.card (AddSubgroup.torsionBy W.toAffine.Point m) := by
  let _ : Algebra F ℝ := e.toRingHom.toAlgebra
  let eqv : W.toAffine.Point ≃+ (W⁄ℝ).toAffine.Point :=
    (Affine.Point.equivBaseChangeSelf W.toAffine).trans
      (Affine.Point.mapEquiv W (AlgEquiv.ofRingEquiv (f := e) fun _ => rfl))
  rw [eqv.index_range_nsmulAddMonoidHom m, (W⁄ℝ).mul_index_range_nsmul_eq_natCard_torsionBy hm]
  exact Nat.card_congr (AddEquiv.torsionByCongr eqv.symm (m : ℤ)).toEquiv

private def tateWeilPairingOfH2MuHom {m : ℕ} (hm : IsUnit (m : F))
    (h : continuousCohomology 2 (muNRep m F) →+ ZMod m) :
    H1 (Gal F) (W.TorsionCoeff m) →+ H1 (Gal F) (W.TorsionCoeff m) →+ ZMod m :=
  (AddMonoidHom.compHom (h.comp (muNRepH2Equiv m F).toAddMonoidHom)).comp
    (W.torsionH1WeilPairing m hm)

private theorem toRatAddCircle_tateWeilPairingOfH2MuHom {m : ℕ} (hm : IsUnit (m : F))
    {hm' : IsUnit (m : F)} (h : continuousCohomology 2 (muNRep m F) →+ ZMod m)
    (inv : Br F →+ AddCircle (1 : ℚ))
    (hinv : ∀ c, ZMod.toRatAddCircle m (h c) = inv (h2MuToBr m F c))
    (a b : H1 (Gal F) (W.TorsionCoeff m)) :
    ZMod.toRatAddCircle m (W.tateWeilPairingOfH2MuHom hm h a b) =
      inv (W.torsionWeilBrauerPairing m hm' a b) := by
  cases Subsingleton.elim hm hm'
  simp only [tateWeilPairingOfH2MuHom, AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply,
    AddEquiv.coe_toAddMonoidHom, hinv, W.torsionWeilBrauerPairing_apply m hm]

private theorem tateWeilPairingOfH2MuHom_eq_zero {m : ℕ} (hm : IsUnit (m : F))
    {h : continuousCohomology 2 (muNRep m F) →+ ZMod m} (hh : h = 0) :
    W.tateWeilPairingOfH2MuHom hm h = 0 := by
  subst hh
  ext a b
  simp [tateWeilPairingOfH2MuHom]

private theorem tateWeilPairingOfH2MuHom_bijective {m : ℕ} [NeZero m] (hm : IsUnit (m : F))
    (h : continuousCohomology 2 (muNRep m F) →+ ZMod m)
    (pair : H1 (Gal F) (W.TorsionCoeff m) →+
      H1 (Gal F) (InternalHom (Gal F) (W.TorsionCoeff m) (KummerCoeff F m)) →+ ZMod m)
    (hpair_apply : ∀ x y, pair x y = h (muNRepH2Equiv m F
      (dualityMap1 (Gal F) (W.TorsionCoeff m) (KummerCoeff F m) x y)))
    (hpair : Function.Bijective pair) : Function.Bijective (W.tateWeilPairingOfH2MuHom hm h) := by
  apply AddMonoidHom.bijective_of_bijective_pairing pair (W.tateWeilPairingOfH2MuHom hm h)
    (AddMonoidHom.id _) (explicitCoeff1 _ _ (W.torsionCoeffWeilDual m hm)
      continuous_of_discreteTopology) (AddMonoidHom.id _) Function.bijective_id
    (explicitCoeff1_bijective _ _ (W.torsionCoeffWeilDual_bijective m hm))
    Function.bijective_id hpair
  intro a b
  simp only [tateWeilPairingOfH2MuHom, AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply,
    AddEquiv.coe_toAddMonoidHom, torsionH1WeilPairing_eq_dualityMap1, hpair_apply,
    AddMonoidHom.id_apply]

private theorem tateWeilPairingOfH2MuHom_kummerMap_kummerMap_eq_zero [DecidableEq F] {m : ℕ}
    (hm : IsUnit (m : F)) {hm' : IsUnit (m : F)}
    (h : continuousCohomology 2 (muNRep m F) →+ ZMod m) (P Q : W.toAffine.Point) :
    W.tateWeilPairingOfH2MuHom hm h (W.kummerMap m hm' P) (W.kummerMap m hm' Q) = 0 := by
  cases Subsingleton.elim hm hm'
  simp only [tateWeilPairingOfH2MuHom, AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply,
    W.torsionH1WeilPairing_kummerMap_kummerMap_eq_zero m hm, map_zero]

private theorem tateWeilPairingOfH2MuHom_eq_zero_of_mem_range_kummerMap [DecidableEq F] {m : ℕ}
    (hm : IsUnit (m : F)) {hm' : IsUnit (m : F)}
    (h : continuousCohomology 2 (muNRep m F) →+ ZMod m) {a b : H1 (Gal F) (W.TorsionCoeff m)}
    (ha : a ∈ (W.kummerMap m hm').range) (hb : b ∈ (W.kummerMap m hm').range) :
    W.tateWeilPairingOfH2MuHom hm h a b = 0 := by
  rcases ha with ⟨P, rfl⟩
  rcases hb with ⟨Q, rfl⟩
  exact W.tateWeilPairingOfH2MuHom_kummerMap_kummerMap_eq_zero hm h P Q

private theorem natCard_torsionBy_zero_eq_zero [DecidableEq F] [CharZero F]
    (hcase : Nonempty (F ≃+* ℝ) ∨ Subsingleton (Gal F)) :
    Nat.card (AddSubgroup.torsionBy W.toAffine.Point (0 : ℤ)) = 0 := by
  have : Infinite W.toAffine.Point := not_finite_iff_infinite.mp fun _ => by
    let k : ℕ := Nat.card W.toAffine.Point + 1
    have hk0 : k ≠ 0 := by omega
    have hkle : Nat.card (AddSubgroup.torsionBy W.toAffine.Point k) ≤
        Nat.card W.toAffine.Point := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (AddSubgroup.torsionBy W.toAffine.Point k)]
      exact Nat.le_mul_of_pos_left _ Nat.card_pos
    rcases hcase with ⟨⟨e⟩⟩ | _
    · have hidx := W.mul_index_range_nsmul_eq_natCard_torsionBy_of_ringEquivReal e hk0
      have : k ≤ Nat.card (AddSubgroup.torsionBy W.toAffine.Point k) :=
        hidx ▸ Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero AddSubgroup.index_ne_zero_of_finite)
      omega
    · have : NeZero k := ⟨hk0⟩
      have he0 : AddSubgroup.torsionBy W.toAffine.Point k ≃+ W.TorsionCoeff k :=
        AddEquiv.ofBijective (W.baseTorsionCoeff k) ⟨W.baseTorsionCoeff_injective k, fun Q =>
          W.exists_baseTorsionCoeff_eq_of_forall_smul_eq fun σ => by
            rw [Subsingleton.elim σ 1, one_smul]⟩
      rw [Nat.card_congr he0.toEquiv, W.natCard_torsionCoeff (unit_natCast k), sq] at hkle
      have : k ≤ k * k := Nat.le_mul_of_pos_left k (by omega)
      omega
  have htop : AddSubgroup.torsionBy W.toAffine.Point (0 : ℤ) = ⊤ := by ext; simp
  rw [htop, Nat.card_congr (AddSubgroup.topEquiv (G := W.toAffine.Point)).toEquiv,
    Nat.card_eq_zero_of_infinite]

private theorem pow_two_mul_natCard_H1_torsionCoeff_of_euler [DecidableEq F] {m : ℕ}
    (hm : IsUnit (m : F)) {k : ℕ}
    (heuler : Nat.card (W.TorsionCoeff m) ^ k * Nat.card (H1 (Gal F) (W.TorsionCoeff m)) =
      Nat.card (H0 (Gal F) (W.TorsionCoeff m)) *
        Nat.card (H0 (Gal F) (InternalHom (Gal F) (W.TorsionCoeff m) (KummerCoeff F m)))) :
    m ^ (2 * k) * Nat.card (H1 (Gal F) (W.TorsionCoeff m)) =
      Nat.card (AddSubgroup.torsionBy W.toAffine.Point m) ^ 2 := by
  have e₀ : AddSubgroup.torsionBy W.toAffine.Point m ≃+ H0 (Gal F) (W.TorsionCoeff m) :=
    AddEquiv.ofBijective
      ((W.baseTorsionCoeff m).codRestrict _ fun T =>
        (FixedPoints.mem_addSubgroup _ _ _).2 fun σ => W.smul_baseTorsionCoeff σ T)
      ⟨fun _ _ h => W.baseTorsionCoeff_injective m (congrArg Subtype.val h), fun Q => by
        obtain ⟨T, hT⟩ := W.exists_baseTorsionCoeff_eq_of_forall_smul_eq
          ((FixedPoints.mem_addSubgroup _ _ _).1 Q.2)
        exact ⟨T, Subtype.ext hT⟩⟩
  have hdual :
      Nat.card (H0 (Gal F) (InternalHom (Gal F) (W.TorsionCoeff m) (KummerCoeff F m))) =
        Nat.card (H0 (Gal F) (W.TorsionCoeff m)) :=
    (Nat.card_congr (Equiv.ofBijective _
      (explicitCoeff0_bijective _ _ (W.torsionCoeffWeilDual_bijective m hm)))).symm
  rw [pow_mul, ← W.natCard_torsionCoeff hm, heuler, hdual, ← sq, Nat.card_congr e₀.toEquiv]

private theorem natCard_ker_torsionCoeffIncl_sq_eq_natCard_H1 [DecidableEq F] {m : ℕ} [NeZero m]
    (hm : IsUnit (m : F)) {k : ℕ}
    (heuler : m ^ (2 * k) * Nat.card (H1 (Gal F) (W.TorsionCoeff m)) =
      Nat.card (AddSubgroup.torsionBy W.toAffine.Point m) ^ 2)
    (hcase : (k = 1 ∧ m * (nsmulAddMonoidHom (α := W.toAffine.Point) m).range.index =
        Nat.card (AddSubgroup.torsionBy W.toAffine.Point m)) ∨ Subsingleton (Gal F)) :
    Nat.card (explicitCoeff1 _ _ (W.torsionCoeffIncl m) continuous_of_discreteTopology).ker ^ 2 =
      Nat.card (H1 (Gal F) (W.TorsionCoeff m)) := by
  rcases hcase with ⟨rfl, hidx⟩ | _
  · rw [← W.range_kummerMap m hm, ← AddSubgroup.index_ker, W.ker_kummerMap m hm]
    refine Nat.eq_of_mul_eq_mul_left (pos_iff_ne_zero.mpr (pow_ne_zero 2 (NeZero.ne m))) ?_
    rw [mul_one] at heuler
    rw [← mul_pow, hidx, heuler]
  · have h1 := subsingleton_H1_of_subsingleton (Gal F) (W.TorsionCoeff m)
    rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩,
      Nat.card_eq_one_iff_unique.mpr ⟨h1, ⟨0⟩⟩, one_pow]

private theorem natCard_range_kummerMap_sq_eq_natCard_H1 [DecidableEq F] {m : ℕ}
    (hm : IsUnit (m : F))
    (hker : Nat.card (explicitCoeff1 _ _ (W.torsionCoeffIncl m)
      continuous_of_discreteTopology).ker ^ 2 = Nat.card (H1 (Gal F) (W.TorsionCoeff m))) :
    Nat.card (W.kummerMap m hm).range ^ 2 = Nat.card (H1 (Gal F) (W.TorsionCoeff m)) := by
  rw [W.range_kummerMap m hm, hker]

private theorem ker_torsionCoeffIncl_eq_ker_tateWeilPairingOfH2MuHom [Finite (Gal F)] {m : ℕ}
    [NeZero m] (hm : IsUnit (m : F)) (h : continuousCohomology 2 (muNRep m F) →+ ZMod m)
    (hbij : Function.Bijective (W.tateWeilPairingOfH2MuHom hm h))
    (hcard : Nat.card (explicitCoeff1 _ _ (W.torsionCoeffIncl m)
      continuous_of_discreteTopology).ker ^ 2 = Nat.card (H1 (Gal F) (W.TorsionCoeff m))) :
    (explicitCoeff1 _ _ (W.torsionCoeffIncl m) continuous_of_discreteTopology).ker =
      ((W.tateWeilPairingOfH2MuHom hm h).compl₂ (explicitCoeff1 _ _ (W.torsionCoeffIncl m)
        continuous_of_discreteTopology).ker.subtype).ker := by
  let : DecidableEq F := Classical.decEq F
  have : Finite (Z1 (Gal F) (W.TorsionCoeff m)) := Subtype.finite
  have : Finite (H1 (Gal F) (W.TorsionCoeff m)) := Quotient.finite _
  let pair := W.tateWeilPairingOfH2MuHom hm h
  refine (pair.eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod hbij
    (nsmul_H1_eq_zero fun P => AddSubgroup.torsionBy.nsmul P) _ _).mpr ⟨fun a ha b hb => ?_, ?_⟩
  · rw [← W.range_kummerMap m hm] at ha hb
    exact W.tateWeilPairingOfH2MuHom_eq_zero_of_mem_range_kummerMap hm h ha hb
  · rw [← sq, hcard]

private theorem range_kummerMap_eq_ker_compl₂ [DecidableEq F] {m : ℕ} (hm : IsUnit (m : F))
    (pair : H1 (Gal F) (W.TorsionCoeff m) →+ H1 (Gal F) (W.TorsionCoeff m) →+ ZMod m)
    (hker : (explicitCoeff1 _ _ (W.torsionCoeffIncl m) continuous_of_discreteTopology).ker =
      (pair.compl₂ (explicitCoeff1 _ _ (W.torsionCoeffIncl m)
        continuous_of_discreteTopology).ker.subtype).ker) :
    (W.kummerMap m hm).range = (pair.compl₂ (W.kummerMap m hm).range.subtype).ker := by
  rw [W.range_kummerMap m hm]
  exact hker

end AbstractField

section Real

variable (W : WeierstrassCurve ℝ) [W.IsElliptic] (m : ℕ) [NeZero m]

/-- **Real local Tate pairing for `E[m]`**, valued in `ZMod m`. -/
def realTateWeilPairing : H1 (AbsoluteGaloisGroup ℝ) (W.TorsionCoeff m) →+
    H1 (AbsoluteGaloisGroup ℝ) (W.TorsionCoeff m) →+ ZMod m :=
  W.tateWeilPairingOfH2MuHom (unit_natCast m) (realH2MuToZMod m)

/-- `realTateWeilPairing` applies `realH2MuToZMod m` to the Weil cup product. -/
@[simp]
theorem realTateWeilPairing_apply (a b : H1 (AbsoluteGaloisGroup ℝ) (W.TorsionCoeff m)) :
    W.realTateWeilPairing m a b = realH2MuToZMod m (muNRepH2Equiv m ℝ
      (W.torsionH1WeilPairing m (Nat.cast_ne_zero.mpr (NeZero.ne m)).isUnit a b)) :=
  (rfl)

/-- In `ℚ/ℤ`, `realTateWeilPairing` is the real Brauer invariant of the Weil cup product. -/
theorem toRatAddCircle_realTateWeilPairing {hm : IsUnit (m : ℝ)}
    (a b : H1 (AbsoluteGaloisGroup ℝ) (W.TorsionCoeff m)) :
    ZMod.toRatAddCircle m (W.realTateWeilPairing m a b) =
      realInv (W.torsionWeilBrauerPairing m hm a b) :=
  W.toRatAddCircle_tateWeilPairingOfH2MuHom (unit_natCast m) (realH2MuToZMod m) realInv
    (toRatAddCircle_realH2MuToZMod m) a b

/-- **Perfect real local Tate duality for `E[m]`.** -/
theorem realTateWeilPairing_bijective : Function.Bijective (W.realTateWeilPairing m) :=
  W.tateWeilPairingOfH2MuHom_bijective (unit_natCast m) (realH2MuToZMod m)
    (realTatePairing (W.TorsionCoeff m) m) (realTatePairing_apply (W.TorsionCoeff m) m)
    (realTatePairing_bijective fun P => AddSubgroup.torsionBy.nsmul P)

/-- **The real Kummer image is isotropic for real Tate duality.** -/
theorem realTateWeilPairing_kummerMap_kummerMap_eq_zero {hm : IsUnit (m : ℝ)}
    (P Q : W.toAffine.Point) :
    W.realTateWeilPairing m (W.kummerMap m hm P) (W.kummerMap m hm Q) = 0 :=
  W.tateWeilPairingOfH2MuHom_kummerMap_kummerMap_eq_zero (unit_natCast m) (realH2MuToZMod m) P Q

/-- Classes in the real Kummer image pair to zero under `realTateWeilPairing`. -/
theorem realTateWeilPairing_eq_zero_of_mem_range_kummerMap {hm : IsUnit (m : ℝ)}
    {a b : H1 (AbsoluteGaloisGroup ℝ) (W.TorsionCoeff m)}
    (ha : a ∈ (W.kummerMap m hm).range) (hb : b ∈ (W.kummerMap m hm).range) :
    W.realTateWeilPairing m a b = 0 :=
  W.tateWeilPairingOfH2MuHom_eq_zero_of_mem_range_kummerMap (unit_natCast m) (realH2MuToZMod m) ha
    hb

omit [NeZero m] in
/-- **Real local Euler characteristic for `E[m]`:** `m ^ 2 · #H¹(G_ℝ, E[m]) = #E(ℝ)[m] ^ 2`. -/
theorem mul_sq_natCard_H1_torsionCoeff_real :
    m ^ 2 * Nat.card (H1 (AbsoluteGaloisGroup ℝ) (W.TorsionCoeff m)) =
      Nat.card (AddSubgroup.torsionBy W.toAffine.Point m) ^ 2 := by
  rcases eq_or_ne m 0 with rfl | hm0
  · rw [zero_pow (by decide), zero_mul, Nat.cast_zero,
      W.natCard_torsionBy_zero_eq_zero (Or.inl ⟨RingEquiv.refl ℝ⟩), sq, mul_zero]
  · have : NeZero m := ⟨hm0⟩
    simpa only [mul_one] using (W.pow_two_mul_natCard_H1_torsionCoeff_of_euler (unit_natCast m)
      (k := 1) (by simpa only [pow_one] using (natCard_mul_natCard_H1_real (A := W.TorsionCoeff m)
        (n := m) fun P => AddSubgroup.torsionBy.nsmul P)))

omit [NeZero m] in
/-- Over `ℝ`, the square of the order of the Kummer image equals `#H¹(G_ℝ, E[m])`. -/
theorem natCard_range_kummerMap_sq_eq_natCard_H1_real (hm : IsUnit (m : ℝ)) :
    Nat.card (W.kummerMap m hm).range ^ 2 =
      Nat.card (H1 (AbsoluteGaloisGroup ℝ) (W.TorsionCoeff m)) :=
  have := hm.neZero_natCast
  W.natCard_range_kummerMap_sq_eq_natCard_H1 hm <|
    W.natCard_ker_torsionCoeffIncl_sq_eq_natCard_H1 hm (k := 1)
      (by simpa only [mul_one] using W.mul_sq_natCard_H1_torsionCoeff_real m)
      (Or.inl ⟨rfl, W.mul_index_range_nsmul_eq_natCard_torsionBy (NeZero.ne m)⟩)

/-- **The real Selmer local condition for `E[m]` is self-orthogonal** for `realTateWeilPairing`. -/
theorem ker_torsionCoeffIncl_eq_ker_realTateWeilPairing :
    (explicitCoeff1 _ _ (W.torsionCoeffIncl m) continuous_of_discreteTopology).ker =
      ((W.realTateWeilPairing m).compl₂
        (explicitCoeff1 _ _ (W.torsionCoeffIncl m)
          continuous_of_discreteTopology).ker.subtype).ker :=
  W.ker_torsionCoeffIncl_eq_ker_tateWeilPairingOfH2MuHom (unit_natCast m) (realH2MuToZMod m)
    (W.realTateWeilPairing_bijective m)
    (W.natCard_ker_torsionCoeffIncl_sq_eq_natCard_H1 (unit_natCast m) (k := 1)
      (by simpa only [mul_one] using W.mul_sq_natCard_H1_torsionCoeff_real m)
      (Or.inl ⟨rfl, W.mul_index_range_nsmul_eq_natCard_torsionBy (NeZero.ne m)⟩))

/-- **The real Kummer image for `E[m]` is its own annihilator** under `realTateWeilPairing`. -/
theorem range_kummerMap_eq_ker_realTateWeilPairing (hm : IsUnit (m : ℝ)) :
    (W.kummerMap m hm).range =
      ((W.realTateWeilPairing m).compl₂ (W.kummerMap m hm).range.subtype).ker :=
  W.range_kummerMap_eq_ker_compl₂ hm (W.realTateWeilPairing m)
    (W.ker_torsionCoeffIncl_eq_ker_realTateWeilPairing m)

end Real

section InfinitePlace

variable {K : Type*} [Field K] {w : InfinitePlace K}
  (W : WeierstrassCurve w.Completion) [W.IsElliptic]

private theorem real_index_or_subsingleton_completion [DecidableEq w.Completion]
    (m : ℕ) [NeZero m] :
    (w.mult = 1 ∧ m * (nsmulAddMonoidHom (α := W.toAffine.Point) m).range.index =
        Nat.card (AddSubgroup.torsionBy W.toAffine.Point m)) ∨
      Subsingleton (AbsoluteGaloisGroup w.Completion) :=
  w.isReal_or_isComplex.imp
    (fun hw => ⟨hw.mult_eq_one,
      W.mul_index_range_nsmul_eq_natCard_torsionBy_of_ringEquivReal
        (Completion.ringEquivRealOfIsReal hw) (NeZero.ne m)⟩)
    fun hw => (Completion.ringEquivComplexOfIsComplex
      hw).absoluteGaloisGroupCongr.symm.toEquiv.subsingleton

variable (m : ℕ) [NeZero m]

/-- **Archimedean local Tate pairing for `E[m]` at an infinite place `w`**, valued in `ZMod m`. -/
def infiniteTateWeilPairing : H1 (AbsoluteGaloisGroup w.Completion) (W.TorsionCoeff m) →+
    H1 (AbsoluteGaloisGroup w.Completion) (W.TorsionCoeff m) →+ ZMod m :=
  have := (Completion.extensionEmbedding w).charZero
  W.tateWeilPairingOfH2MuHom (unit_natCast m) (infiniteH2MuToZMod w m)

/-- `infiniteTateWeilPairing` applies `infiniteH2MuToZMod w m` to the Weil cup product. -/
@[simp]
theorem infiniteTateWeilPairing_apply
    (a b : H1 (AbsoluteGaloisGroup w.Completion) (W.TorsionCoeff m)) :
    W.infiniteTateWeilPairing m a b = infiniteH2MuToZMod w m (muNRepH2Equiv m w.Completion
      (W.torsionH1WeilPairing m (by have := (Completion.extensionEmbedding w).charZero
                                    exact (Nat.cast_ne_zero.mpr (NeZero.ne m)).isUnit) a b)) :=
  (rfl)

/-- In `ℚ/ℤ`, `infiniteTateWeilPairing` is the archimedean Brauer invariant of the Weil cup. -/
theorem toRatAddCircle_infiniteTateWeilPairing {hm : IsUnit (m : w.Completion)}
    (a b : H1 (AbsoluteGaloisGroup w.Completion) (W.TorsionCoeff m)) :
    ZMod.toRatAddCircle m (W.infiniteTateWeilPairing m a b) =
      infiniteInvMap w (W.torsionWeilBrauerPairing m hm a b) :=
  have := (Completion.extensionEmbedding w).charZero
  W.toRatAddCircle_tateWeilPairingOfH2MuHom (unit_natCast m) (infiniteH2MuToZMod w m)
    (infiniteInvMap w) (toRatAddCircle_infiniteH2MuToZMod w m) a b

/-- At a complex place, `infiniteTateWeilPairing` is the zero homomorphism. -/
@[simp]
theorem infiniteTateWeilPairing_of_isComplex (hw : w.IsComplex) :
    W.infiniteTateWeilPairing m = 0 :=
  have := (Completion.extensionEmbedding w).charZero
  W.tateWeilPairingOfH2MuHom_eq_zero (unit_natCast m) (infiniteH2MuToZMod_of_isComplex w m hw)

/-- **Perfect archimedean local Tate duality for `E[m]`.** -/
theorem infiniteTateWeilPairing_bijective : Function.Bijective (W.infiniteTateWeilPairing m) :=
  have := (Completion.extensionEmbedding w).charZero
  W.tateWeilPairingOfH2MuHom_bijective (unit_natCast m) (infiniteH2MuToZMod w m)
    (infiniteTatePairing w (W.TorsionCoeff m) m) (infiniteTatePairing_apply w (W.TorsionCoeff m) m)
    (infiniteTatePairing_bijective w fun P => AddSubgroup.torsionBy.nsmul P)

/-- **The local Kummer image at an infinite place is isotropic for archimedean Tate duality.** -/
theorem infiniteTateWeilPairing_kummerMap_kummerMap_eq_zero [DecidableEq w.Completion]
    {hm : IsUnit (m : w.Completion)} (P Q : W.toAffine.Point) :
    W.infiniteTateWeilPairing m (W.kummerMap m hm P) (W.kummerMap m hm Q) = 0 :=
  have := (Completion.extensionEmbedding w).charZero
  W.tateWeilPairingOfH2MuHom_kummerMap_kummerMap_eq_zero (unit_natCast m) (infiniteH2MuToZMod w m)
    P Q

/-- Classes in the local Kummer image at `w` pair to zero under `infiniteTateWeilPairing`. -/
theorem infiniteTateWeilPairing_eq_zero_of_mem_range_kummerMap [DecidableEq w.Completion]
    {hm : IsUnit (m : w.Completion)}
    {a b : H1 (AbsoluteGaloisGroup w.Completion) (W.TorsionCoeff m)}
    (ha : a ∈ (W.kummerMap m hm).range) (hb : b ∈ (W.kummerMap m hm).range) :
    W.infiniteTateWeilPairing m a b = 0 :=
  have := (Completion.extensionEmbedding w).charZero
  W.tateWeilPairingOfH2MuHom_eq_zero_of_mem_range_kummerMap (unit_natCast m)
    (infiniteH2MuToZMod w m) ha hb

omit [NeZero m] in
/-- **Archimedean Euler characteristic:** `m ^ (2 * w.mult) · #H¹(K_w, E[m]) = #E(K_w)[m]²`. -/
theorem pow_two_mul_mult_mul_natCard_H1_torsionCoeff_completion [DecidableEq w.Completion] :
    m ^ (2 * w.mult) * Nat.card (H1 (AbsoluteGaloisGroup w.Completion) (W.TorsionCoeff m)) =
      Nat.card (AddSubgroup.torsionBy W.toAffine.Point m) ^ 2 := by
  have := (Completion.extensionEmbedding w).charZero
  rcases eq_or_ne m 0 with rfl | hm0
  · have hmult : 2 * w.mult ≠ 0 :=
      w.isReal_or_isComplex.elim (fun hw => by simp [hw.mult_eq_one])
        (fun hw => by simp [hw.mult_eq_two])
    have hcase : Nonempty (w.Completion ≃+* ℝ) ∨ Subsingleton (AbsoluteGaloisGroup w.Completion) :=
      w.isReal_or_isComplex.imp (fun hw => ⟨Completion.ringEquivRealOfIsReal hw⟩) fun hw =>
        (Completion.ringEquivComplexOfIsComplex
          hw).absoluteGaloisGroupCongr.symm.toEquiv.subsingleton
    rw [zero_pow hmult, zero_mul, Nat.cast_zero, W.natCard_torsionBy_zero_eq_zero hcase, sq,
      mul_zero]
  · have : NeZero m := ⟨hm0⟩
    exact W.pow_two_mul_natCard_H1_torsionCoeff_of_euler (unit_natCast m) (k := w.mult)
      (natCard_pow_mult_mul_natCard_H1_completion w (A := W.TorsionCoeff m) (n := m)
        fun P => AddSubgroup.torsionBy.nsmul P)

omit [NeZero m] in
/-- At every infinite place `w`, `#H¹_m(K_w) ^ 2 = #H¹(K_w, E[m])`. -/
theorem natCard_range_kummerMap_sq_eq_natCard_H1_completion [DecidableEq w.Completion]
    (hm : IsUnit (m : w.Completion)) :
    Nat.card (W.kummerMap m hm).range ^ 2 =
      Nat.card (H1 (AbsoluteGaloisGroup w.Completion) (W.TorsionCoeff m)) :=
  have := hm.neZero_natCast
  W.natCard_range_kummerMap_sq_eq_natCard_H1 hm <|
    W.natCard_ker_torsionCoeffIncl_sq_eq_natCard_H1 hm (k := w.mult)
      (W.pow_two_mul_mult_mul_natCard_H1_torsionCoeff_completion m)
      (real_index_or_subsingleton_completion W m)

/-- **The Selmer local condition for `E[m]` at `w` is its own exact annihilator.** -/
theorem ker_torsionCoeffIncl_eq_ker_infiniteTateWeilPairing :
    (explicitCoeff1 _ _ (W.torsionCoeffIncl m) continuous_of_discreteTopology).ker =
      ((W.infiniteTateWeilPairing m).compl₂
        (explicitCoeff1 _ _ (W.torsionCoeffIncl m)
          continuous_of_discreteTopology).ker.subtype).ker := by
  let : DecidableEq w.Completion := Classical.decEq w.Completion
  have := (Completion.extensionEmbedding w).charZero
  have := finite_galois_completion w
  exact W.ker_torsionCoeffIncl_eq_ker_tateWeilPairingOfH2MuHom (unit_natCast m)
    (infiniteH2MuToZMod w m) (W.infiniteTateWeilPairing_bijective m)
    (W.natCard_ker_torsionCoeffIncl_sq_eq_natCard_H1 (unit_natCast m) (k := w.mult)
      (W.pow_two_mul_mult_mul_natCard_H1_torsionCoeff_completion m)
      (real_index_or_subsingleton_completion W m))

/-- **The local Kummer image for `E[m]` at `w` is its own exact annihilator.** -/
theorem range_kummerMap_eq_ker_infiniteTateWeilPairing [DecidableEq w.Completion]
    (hm : IsUnit (m : w.Completion)) :
    (W.kummerMap m hm).range =
      ((W.infiniteTateWeilPairing m).compl₂ (W.kummerMap m hm).range.subtype).ker :=
  W.range_kummerMap_eq_ker_compl₂ hm (W.infiniteTateWeilPairing m)
    (W.ker_torsionCoeffIncl_eq_ker_infiniteTateWeilPairing m)

end InfinitePlace

end WeierstrassCurve

namespace TauCeti.Isogeny

open WeierstrassCurve Hom

private theorem deg_isUnit {F : Type*} [Field F] [CharZero F] {W₁ W₂ : WeierstrassCurve F}
    (φ : Isogeny W₁.toAffine W₂.toAffine) : IsUnit (φ.degree : F) :=
  (Nat.cast_ne_zero.mpr φ.degree_ne_zero).isUnit

section AbstractField

local notation "Gal" => AbsoluteGaloisGroup

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

private theorem degree_mul_index_range_mul_dual_of_ringEquivReal [DecidableEq F] (e : F ≃+* ℝ) :
    φ.degree * ((ofIsogeny φ).pointMapHom.range.index *
        (ofIsogeny φ.dual).pointMapHom.range.index) =
      Nat.card (ofIsogeny φ).pointMapHom.ker * Nat.card (ofIsogeny φ.dual).pointMapHom.ker := by
  rw [← Hom.dual_ofIsogeny, ← Hom.degree_ofIsogeny]
  set f := ofIsogeny φ
  have hn : f.degree ≠ 0 := f.degree_eq_zero_iff.not.mpr (Hom.ofIsogeny_ne_zero φ)
  have hidx := W₁.mul_index_range_nsmul_eq_natCard_torsionBy_of_ringEquivReal e hn
  have : Finite (Submodule.torsionBy ℤ W₁.toAffine.Point f.degree) :=
    W₁.finite_torsionBy (Int.natCast_ne_zero.mpr hn)
  have h := f.index_range_nsmul_mul_card_ker_mul_card_ker_dual
  rw [TauCeti.natCard_ker_nsmulAddMonoidHom_eq_natCard_torsionBy] at h
  refine Nat.eq_of_mul_eq_mul_left
    (Nat.card_pos (α := Submodule.torsionBy ℤ W₁.toAffine.Point f.degree)) ?_
  linear_combination f.degree * h.symm +
    (Nat.card f.pointMapHom.ker * Nat.card f.dual.pointMapHom.ker) * hidx

private def tateKerWeilPairingOfH2MuHom (hn : IsUnit (φ.degree : F))
    (h : continuousCohomology 2 (muNRep φ.degree F) →+ ZMod φ.degree) :
    H1 (Gal F) (ofIsogeny φ).KerCoeff →+ H1 (Gal F) (ofIsogeny φ.dual).KerCoeff →+ ZMod φ.degree :=
  (AddMonoidHom.compHom (h.comp (muNRepH2Equiv φ.degree F).toAddMonoidHom)).comp
    (φ.kerH1WeilPairing hn)

private theorem tateKerWeilPairingOfH2MuHom_eq_zero (hn : IsUnit (φ.degree : F))
    {h : continuousCohomology 2 (muNRep φ.degree F) →+ ZMod φ.degree} (hh : h = 0) :
    φ.tateKerWeilPairingOfH2MuHom hn h = 0 := by
  subst hh
  ext a b
  simp [tateKerWeilPairingOfH2MuHom]

private theorem tateKerWeilPairingOfH2MuHom_explicitCoeff1_torsionCoeffToDualKerCoeff
    (hn : IsUnit (φ.degree : F)) (h : continuousCohomology 2 (muNRep φ.degree F) →+ ZMod φ.degree)
    (a : H1 (Gal F) (ofIsogeny φ).KerCoeff) (b : H1 (Gal F) (W₁.TorsionCoeff φ.degree)) :
    φ.tateKerWeilPairingOfH2MuHom hn h a
        (explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology b) =
      W₁.tateWeilPairingOfH2MuHom hn h
        (explicitCoeff1 _ _ φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology a) b := by
  simp [tateKerWeilPairingOfH2MuHom, WeierstrassCurve.tateWeilPairingOfH2MuHom,
    kerH1WeilPairing_explicitCoeff1_torsionCoeffToDualKerCoeff]

private theorem tateKerWeilPairingOfH2MuHom_bijective (hn : IsUnit (φ.degree : F))
    (h : continuousCohomology 2 (muNRep φ.degree F) →+ ZMod φ.degree)
    (pair : H1 (Gal F) (ofIsogeny φ).KerCoeff →+
      H1 (Gal F) (InternalHom (Gal F) (ofIsogeny φ).KerCoeff (KummerCoeff F φ.degree)) →+
        ZMod φ.degree)
    (hpair_apply : ∀ x y, pair x y = h (muNRepH2Equiv φ.degree F
      (dualityMap1 (Gal F) (ofIsogeny φ).KerCoeff (KummerCoeff F φ.degree) x y)))
    (hpair : Function.Bijective pair) :
    Function.Bijective (φ.tateKerWeilPairingOfH2MuHom hn h) := by
  apply AddMonoidHom.bijective_of_bijective_pairing pair (φ.tateKerWeilPairingOfH2MuHom hn h)
    (AddMonoidHom.id _) (explicitCoeff1 _ _ (φ.kerCoeffWeilDual hn) continuous_of_discreteTopology)
    (AddMonoidHom.id _) Function.bijective_id
    (explicitCoeff1_bijective _ _ (φ.kerCoeffWeilDual_bijective hn)) Function.bijective_id hpair
  intro a b
  simp only [tateKerWeilPairingOfH2MuHom, AddMonoidHom.comp_apply,
    AddMonoidHom.compHom_apply_apply, AddEquiv.coe_toAddMonoidHom,
    kerH1WeilPairing_eq_dualityMap1, hpair_apply, AddMonoidHom.id_apply]

private theorem tateKerWeilPairingOfH2MuHom_kummerMap [CharZero F] [DecidableEq F]
    (hn : IsUnit (φ.degree : F)) {hm : IsUnit (φ.degree : F)}
    (h : continuousCohomology 2 (muNRep φ.degree F) →+ ZMod φ.degree)
    (Q : W₂.toAffine.Point) (P : W₁.toAffine.Point) :
    φ.tateKerWeilPairingOfH2MuHom hn h (φ.kummerMap Q) (φ.dual.kummerMap P) =
      W₁.tateWeilPairingOfH2MuHom hn h
        (W₁.kummerMap φ.degree hm ((ofIsogeny φ.dual).pointMap Q))
        (W₁.kummerMap φ.degree hm P) := by
  cases Subsingleton.elim hn hm
  simp only [tateKerWeilPairingOfH2MuHom, WeierstrassCurve.tateWeilPairingOfH2MuHom,
    AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply, φ.kerH1WeilPairing_kummerMap hn]

private theorem tateKerWeilPairingOfH2MuHom_kummerMap_kummerMap_eq_zero [CharZero F] [DecidableEq F]
    (hn : IsUnit (φ.degree : F)) (h : continuousCohomology 2 (muNRep φ.degree F) →+ ZMod φ.degree)
    (Q : W₂.toAffine.Point) (P : W₁.toAffine.Point) :
    φ.tateKerWeilPairingOfH2MuHom hn h (φ.kummerMap Q) (φ.dual.kummerMap P) = 0 := by
  simp only [tateKerWeilPairingOfH2MuHom, AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply,
    φ.kerH1WeilPairing_kummerMap_kummerMap_eq_zero hn, map_zero]

private theorem tateKerWeilPairingOfH2MuHom_eq_zero_of_mem_range_kummerMap [CharZero F]
    [DecidableEq F] (hn : IsUnit (φ.degree : F))
    (h : continuousCohomology 2 (muNRep φ.degree F) →+ ZMod φ.degree)
    {a : H1 (Gal F) (ofIsogeny φ).KerCoeff} {b : H1 (Gal F) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ φ.kummerMap.range) (hb : b ∈ φ.dual.kummerMap.range) :
    φ.tateKerWeilPairingOfH2MuHom hn h a b = 0 := by
  simp only [tateKerWeilPairingOfH2MuHom, AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply,
    φ.kerH1WeilPairing_eq_zero_of_mem_range_kummerMap hn ha hb, map_zero]

private theorem tateKerWeilPairingOfH2MuHom_eq_zero_of_mem_ker (hn : IsUnit (φ.degree : F))
    (h : continuousCohomology 2 (muNRep φ.degree F) →+ ZMod φ.degree)
    {a : H1 (Gal F) (ofIsogeny φ).KerCoeff} {b : H1 (Gal F) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology).ker)
    (hb : b ∈ (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
      continuous_of_discreteTopology).ker) :
    φ.tateKerWeilPairingOfH2MuHom hn h a b = 0 := by
  simp only [tateKerWeilPairingOfH2MuHom, AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply,
    φ.kerH1WeilPairing_eq_zero_of_mem_ker hn ha hb, map_zero]

private theorem degree_pow_mul_natCard_H1_kerCoeff_of_euler [DecidableEq F]
    (hn : IsUnit (φ.degree : F)) {k : ℕ}
    (heuler : Nat.card (ofIsogeny φ).KerCoeff ^ k * Nat.card (H1 (Gal F) (ofIsogeny φ).KerCoeff) =
      Nat.card (H0 (Gal F) (ofIsogeny φ).KerCoeff) *
        Nat.card (H0 (Gal F)
          (InternalHom (Gal F) (ofIsogeny φ).KerCoeff (KummerCoeff F φ.degree)))) :
    φ.degree ^ k * Nat.card (H1 (Gal F) (ofIsogeny φ).KerCoeff) =
      Nat.card (ofIsogeny φ).pointMapHom.ker * Nat.card (ofIsogeny φ.dual).pointMapHom.ker := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have hdual : Nat.card (H0 (Gal F)
      (InternalHom (Gal F) (ofIsogeny φ).KerCoeff (KummerCoeff F φ.degree))) =
      Nat.card (ofIsogeny φ.dual).pointMapHom.ker :=
    (Nat.card_congr (Equiv.ofBijective _
      (explicitCoeff0_bijective _ _ (φ.kerCoeffWeilDual_bijective hn))).symm).trans
      (Nat.card_congr (ofIsogeny φ.dual).kerPointMapEquivInvariants.symm.toEquiv)
  rw [← φ.natCard_kerCoeff_eq_degree, heuler, hdual,
    Nat.card_congr (ofIsogeny φ).kerPointMapEquivInvariants.symm.toEquiv]

private theorem natCard_ker_kerCoeffIncl_mul_dual_eq_natCard_H1 [DecidableEq F]
    (hn : IsUnit (φ.degree : F)) {k : ℕ}
    (heuler : φ.degree ^ k * Nat.card (H1 (Gal F) (ofIsogeny φ).KerCoeff) =
      Nat.card (ofIsogeny φ).pointMapHom.ker * Nat.card (ofIsogeny φ.dual).pointMapHom.ker)
    (hcase : (k = 1 ∧ φ.degree * ((ofIsogeny φ).pointMapHom.range.index *
          (ofIsogeny φ.dual).pointMapHom.range.index) =
        Nat.card (ofIsogeny φ).pointMapHom.ker * Nat.card (ofIsogeny φ.dual).pointMapHom.ker) ∨
      Subsingleton (Gal F)) :
    Nat.card (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology).ker *
      Nat.card (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
        continuous_of_discreteTopology).ker = Nat.card (H1 (Gal F) (ofIsogeny φ).KerCoeff) := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  rcases hcase with ⟨rfl, hidx⟩ | _
  · rw [← φ.range_kummerMap, ← φ.dual.range_kummerMap, natCard_range_kummerMap,
      natCard_range_kummerMap]
    refine Nat.eq_of_mul_eq_mul_left φ.degree_pos ?_
    rw [pow_one] at heuler
    exact hidx.trans heuler.symm
  · have h1 := subsingleton_H1_of_subsingleton (Gal F) (ofIsogeny φ).KerCoeff
    have := subsingleton_H1_of_subsingleton (Gal F) (ofIsogeny φ.dual).KerCoeff
    rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩,
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩,
      Nat.card_eq_one_iff_unique.mpr ⟨h1, ⟨0⟩⟩, mul_one]

private theorem natCard_range_kummerMap_mul_dual_eq_natCard_H1 [CharZero F] [DecidableEq F]
    (hker : Nat.card (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl
        continuous_of_discreteTopology).ker *
      Nat.card (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
        continuous_of_discreteTopology).ker = Nat.card (H1 (Gal F) (ofIsogeny φ).KerCoeff)) :
    Nat.card φ.kummerMap.range * Nat.card φ.dual.kummerMap.range =
      Nat.card (H1 (Gal F) (ofIsogeny φ).KerCoeff) := by
  rw [φ.range_kummerMap, φ.dual.range_kummerMap, hker]

private theorem ker_kerCoeffIncl_eq_ker_tateKerWeilPairingOfH2MuHom [Finite (Gal F)]
    (hn : IsUnit (φ.degree : F)) (h : continuousCohomology 2 (muNRep φ.degree F) →+ ZMod φ.degree)
    (hbij : Function.Bijective (φ.tateKerWeilPairingOfH2MuHom hn h))
    (hcard : Nat.card (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl
        continuous_of_discreteTopology).ker *
      Nat.card (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
        continuous_of_discreteTopology).ker = Nat.card (H1 (Gal F) (ofIsogeny φ).KerCoeff)) :
    (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology).ker =
      ((φ.tateKerWeilPairingOfH2MuHom hn h).compl₂
        (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
          continuous_of_discreteTopology).ker.subtype).ker := by
  have : Finite (Z1 (Gal F) (ofIsogeny φ.dual).KerCoeff) := Subtype.finite
  have : Finite (H1 (Gal F) (ofIsogeny φ.dual).KerCoeff) := Quotient.finite _
  have hkill : ∀ Q : (ofIsogeny φ.dual).KerCoeff, φ.degree • Q = 0 := fun Q => by
    simpa only [degree_dual] using φ.dual.degree_nsmul_kerCoeff_eq_zero Q
  let pair := φ.tateKerWeilPairingOfH2MuHom hn h
  exact (pair.eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod hbij
    (nsmul_H1_eq_zero hkill) _ _).mpr
    ⟨fun _ ha _ hb => φ.tateKerWeilPairingOfH2MuHom_eq_zero_of_mem_ker hn h ha hb, hcard⟩

private theorem range_kummerMap_eq_ker_compl₂ [CharZero F] [DecidableEq F]
    (pair : H1 (Gal F) (ofIsogeny φ).KerCoeff →+
      H1 (Gal F) (ofIsogeny φ.dual).KerCoeff →+ ZMod φ.degree)
    (hker : (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology).ker =
      (pair.compl₂ (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
        continuous_of_discreteTopology).ker.subtype).ker) :
    φ.kummerMap.range = (pair.compl₂ φ.dual.kummerMap.range.subtype).ker := by
  rw [φ.range_kummerMap, φ.dual.range_kummerMap]
  exact hker

end AbstractField

section Real

variable {W₁ W₂ : WeierstrassCurve ℝ} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **Real local Tate pairing for an isogeny `φ` and its dual `φ̂`**, valued in `ZMod φ.degree`. -/
def realTateKerWeilPairing : H1 (AbsoluteGaloisGroup ℝ) (ofIsogeny φ).KerCoeff →+
    H1 (AbsoluteGaloisGroup ℝ) (ofIsogeny φ.dual).KerCoeff →+ ZMod φ.degree :=
  φ.tateKerWeilPairingOfH2MuHom (deg_isUnit φ) (realH2MuToZMod φ.degree)

/-- `realTateKerWeilPairing` applies `realH2MuToZMod φ.degree` to the isogeny Weil cup product. -/
@[simp]
theorem realTateKerWeilPairing_apply (a : H1 (AbsoluteGaloisGroup ℝ) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup ℝ) (ofIsogeny φ.dual).KerCoeff) :
    φ.realTateKerWeilPairing a b = realH2MuToZMod φ.degree (muNRepH2Equiv φ.degree ℝ
      (φ.kerH1WeilPairing (Nat.cast_ne_zero.mpr φ.degree_ne_zero).isUnit a b)) :=
  (rfl)

/-- Compatibility of `realTateKerWeilPairing` with torsion inclusion and dual-kernel projection. -/
theorem realTateKerWeilPairing_explicitCoeff1_torsionCoeffToDualKerCoeff
    (a : H1 (AbsoluteGaloisGroup ℝ) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup ℝ) (W₁.TorsionCoeff φ.degree)) :
    φ.realTateKerWeilPairing a
        (explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology b) =
      W₁.realTateWeilPairing φ.degree
        (explicitCoeff1 _ _ φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology a) b :=
  φ.tateKerWeilPairingOfH2MuHom_explicitCoeff1_torsionCoeffToDualKerCoeff (deg_isUnit φ)
    (realH2MuToZMod φ.degree) a b

/-- On real Kummer classes, `realTateKerWeilPairing` agrees with `realTateWeilPairing`. -/
theorem realTateKerWeilPairing_kummerMap {hm : IsUnit (φ.degree : ℝ)}
    (Q : W₂.toAffine.Point) (P : W₁.toAffine.Point) :
    φ.realTateKerWeilPairing (φ.kummerMap Q) (φ.dual.kummerMap P) =
      W₁.realTateWeilPairing φ.degree (W₁.kummerMap φ.degree hm ((ofIsogeny φ.dual).pointMap Q))
        (W₁.kummerMap φ.degree hm P) :=
  φ.tateKerWeilPairingOfH2MuHom_kummerMap (deg_isUnit φ) (realH2MuToZMod φ.degree) Q P

/-- **Perfect real local Tate duality for the kernels of an isogeny and of its dual.** -/
theorem realTateKerWeilPairing_bijective : Function.Bijective φ.realTateKerWeilPairing :=
  φ.tateKerWeilPairingOfH2MuHom_bijective (deg_isUnit φ) (realH2MuToZMod φ.degree)
    (realTatePairing (ofIsogeny φ).KerCoeff φ.degree)
    (realTatePairing_apply (ofIsogeny φ).KerCoeff φ.degree)
    (realTatePairing_bijective φ.degree_nsmul_kerCoeff_eq_zero)

/-- **The real Kummer images of `φ` and `φ̂` are orthogonal** under `realTateKerWeilPairing`. -/
@[simp↓]
theorem realTateKerWeilPairing_kummerMap_kummerMap_eq_zero
    (Q : W₂.toAffine.Point) (P : W₁.toAffine.Point) :
    φ.realTateKerWeilPairing (φ.kummerMap Q) (φ.dual.kummerMap P) = 0 :=
  φ.tateKerWeilPairingOfH2MuHom_kummerMap_kummerMap_eq_zero (deg_isUnit φ)
    (realH2MuToZMod φ.degree) Q P

/-- Classes in the real Kummer subgroups of `φ` and `φ̂` pair to zero. -/
theorem realTateKerWeilPairing_eq_zero_of_mem_range_kummerMap
    {a : H1 (AbsoluteGaloisGroup ℝ) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup ℝ) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ φ.kummerMap.range) (hb : b ∈ φ.dual.kummerMap.range) :
    φ.realTateKerWeilPairing a b = 0 :=
  φ.tateKerWeilPairingOfH2MuHom_eq_zero_of_mem_range_kummerMap (deg_isUnit φ)
    (realH2MuToZMod φ.degree) ha hb

/-- Classes in the real Selmer local conditions of `φ` and `φ̂` pair to zero. -/
theorem realTateKerWeilPairing_eq_zero_of_mem_ker
    {a : H1 (AbsoluteGaloisGroup ℝ) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup ℝ) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology).ker)
    (hb : b ∈ (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
      continuous_of_discreteTopology).ker) :
    φ.realTateKerWeilPairing a b = 0 :=
  φ.tateKerWeilPairingOfH2MuHom_eq_zero_of_mem_ker (deg_isUnit φ) (realH2MuToZMod φ.degree) ha hb

/-- **Real local Euler characteristic:** `deg φ · #H¹(G_ℝ, E₁[φ]) = #E₁(ℝ)[φ] · #E₂(ℝ)[φ̂]`. -/
theorem degree_mul_natCard_H1_kerCoeff_real :
    φ.degree * Nat.card (H1 (AbsoluteGaloisGroup ℝ) (ofIsogeny φ).KerCoeff) =
      Nat.card (ofIsogeny φ).pointMapHom.ker * Nat.card (ofIsogeny φ.dual).pointMapHom.ker := by
  simpa only [pow_one] using (φ.degree_pow_mul_natCard_H1_kerCoeff_of_euler (deg_isUnit φ) (k := 1)
    (by simpa only [pow_one] using (natCard_mul_natCard_H1_real (A := (ofIsogeny φ).KerCoeff)
      (n := φ.degree) φ.degree_nsmul_kerCoeff_eq_zero)))

/-- Over `ℝ`, `#H¹_φ(ℝ) · #H¹_φ̂(ℝ) = #H¹(G_ℝ, E₁[φ])`. -/
theorem natCard_range_kummerMap_mul_dual_eq_natCard_H1_real :
    Nat.card φ.kummerMap.range * Nat.card φ.dual.kummerMap.range =
      Nat.card (H1 (AbsoluteGaloisGroup ℝ) (ofIsogeny φ).KerCoeff) := by
  refine Nat.eq_of_mul_eq_mul_left φ.degree_pos ?_
  rw [φ.degree_mul_natCard_range_kummerMap_mul_natCard_range_kummerMap_dual,
    φ.degree_mul_natCard_H1_kerCoeff_real]

/-- **The real Selmer local condition of `φ` is the exact annihilator of that of `φ̂`.** -/
theorem ker_kerCoeffIncl_eq_ker_realTateKerWeilPairing :
    (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology).ker =
      (φ.realTateKerWeilPairing.compl₂
        (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
          continuous_of_discreteTopology).ker.subtype).ker :=
  φ.ker_kerCoeffIncl_eq_ker_tateKerWeilPairingOfH2MuHom (deg_isUnit φ) (realH2MuToZMod φ.degree)
    φ.realTateKerWeilPairing_bijective (by
      rw [← φ.range_kummerMap, ← φ.dual.range_kummerMap,
        φ.natCard_range_kummerMap_mul_dual_eq_natCard_H1_real])

/-- **The real Kummer image of `φ` is the exact annihilator of the real Kummer image of `φ̂`.** -/
theorem range_kummerMap_eq_ker_realTateKerWeilPairing :
    φ.kummerMap.range = (φ.realTateKerWeilPairing.compl₂ φ.dual.kummerMap.range.subtype).ker :=
  φ.range_kummerMap_eq_ker_compl₂ φ.realTateKerWeilPairing
    φ.ker_kerCoeffIncl_eq_ker_realTateKerWeilPairing

end Real

section InfinitePlace

variable {K : Type*} [Field K] {w : InfinitePlace K}
  {W₁ W₂ : WeierstrassCurve w.Completion} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

private theorem real_isogeny_index_or_subsingleton_completion [DecidableEq w.Completion] :
    (w.mult = 1 ∧ φ.degree * ((ofIsogeny φ).pointMapHom.range.index *
          (ofIsogeny φ.dual).pointMapHom.range.index) =
        Nat.card (ofIsogeny φ).pointMapHom.ker * Nat.card (ofIsogeny φ.dual).pointMapHom.ker) ∨
      Subsingleton (AbsoluteGaloisGroup w.Completion) :=
  w.isReal_or_isComplex.imp
    (fun hw => ⟨hw.mult_eq_one,
      φ.degree_mul_index_range_mul_dual_of_ringEquivReal (Completion.ringEquivRealOfIsReal hw)⟩)
    fun hw => (Completion.ringEquivComplexOfIsComplex
      hw).absoluteGaloisGroupCongr.symm.toEquiv.subsingleton

/-- **Archimedean local Tate pairing for an isogeny `φ` and its dual `φ̂` at `w`.** -/
def infiniteTateKerWeilPairing :
    H1 (AbsoluteGaloisGroup w.Completion) (ofIsogeny φ).KerCoeff →+
      H1 (AbsoluteGaloisGroup w.Completion) (ofIsogeny φ.dual).KerCoeff →+ ZMod φ.degree :=
  have := (Completion.extensionEmbedding w).charZero
  φ.tateKerWeilPairingOfH2MuHom (deg_isUnit φ) (infiniteH2MuToZMod w φ.degree)

/-- `infiniteTateKerWeilPairing` applies `infiniteH2MuToZMod` to the isogeny Weil cup product. -/
@[simp]
theorem infiniteTateKerWeilPairing_apply
    (a : H1 (AbsoluteGaloisGroup w.Completion) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup w.Completion) (ofIsogeny φ.dual).KerCoeff) :
    φ.infiniteTateKerWeilPairing a b = infiniteH2MuToZMod w φ.degree
      (muNRepH2Equiv φ.degree w.Completion (φ.kerH1WeilPairing
        (by have := (Completion.extensionEmbedding w).charZero
            exact (Nat.cast_ne_zero.mpr φ.degree_ne_zero).isUnit) a b)) :=
  (rfl)

/-- At a complex place, `infiniteTateKerWeilPairing` is the zero homomorphism. -/
@[simp]
theorem infiniteTateKerWeilPairing_of_isComplex (hw : w.IsComplex) :
    φ.infiniteTateKerWeilPairing = 0 :=
  have := (Completion.extensionEmbedding w).charZero
  φ.tateKerWeilPairingOfH2MuHom_eq_zero (deg_isUnit φ)
    (infiniteH2MuToZMod_of_isComplex w φ.degree hw)

/-- Compatibility of `infiniteTateKerWeilPairing` with torsion inclusion and dual projection. -/
theorem infiniteTateKerWeilPairing_explicitCoeff1_torsionCoeffToDualKerCoeff
    (a : H1 (AbsoluteGaloisGroup w.Completion) (ofIsogeny φ).KerCoeff)
    (b : H1 (AbsoluteGaloisGroup w.Completion) (W₁.TorsionCoeff φ.degree)) :
    φ.infiniteTateKerWeilPairing a
        (explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology b) =
      W₁.infiniteTateWeilPairing φ.degree
        (explicitCoeff1 _ _ φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology a) b :=
  have := (Completion.extensionEmbedding w).charZero
  φ.tateKerWeilPairingOfH2MuHom_explicitCoeff1_torsionCoeffToDualKerCoeff (deg_isUnit φ)
    (infiniteH2MuToZMod w φ.degree) a b

/-- On local Kummer classes at `w`, `infiniteTateKerWeilPairing` agrees with torsion Tate. -/
theorem infiniteTateKerWeilPairing_kummerMap [DecidableEq w.Completion]
    {hm : IsUnit (φ.degree : w.Completion)} (Q : W₂.toAffine.Point) (P : W₁.toAffine.Point) :
    have : CharZero w.Completion := (Completion.extensionEmbedding w).charZero
    φ.infiniteTateKerWeilPairing (φ.kummerMap Q) (φ.dual.kummerMap P) =
      W₁.infiniteTateWeilPairing φ.degree
        (W₁.kummerMap φ.degree hm ((ofIsogeny φ.dual).pointMap Q))
        (W₁.kummerMap φ.degree hm P) :=
  have : CharZero w.Completion := (Completion.extensionEmbedding w).charZero
  φ.tateKerWeilPairingOfH2MuHom_kummerMap (deg_isUnit φ) (infiniteH2MuToZMod w φ.degree) Q P

/-- **Perfect archimedean local Tate duality for the kernels of an isogeny and of its dual.** -/
theorem infiniteTateKerWeilPairing_bijective : Function.Bijective φ.infiniteTateKerWeilPairing :=
  have := (Completion.extensionEmbedding w).charZero
  φ.tateKerWeilPairingOfH2MuHom_bijective (deg_isUnit φ) (infiniteH2MuToZMod w φ.degree)
    (infiniteTatePairing w (ofIsogeny φ).KerCoeff φ.degree)
    (infiniteTatePairing_apply w (ofIsogeny φ).KerCoeff φ.degree)
    (infiniteTatePairing_bijective w φ.degree_nsmul_kerCoeff_eq_zero)

/-- **The local Kummer images of `φ` and `φ̂` at `w` are orthogonal** for Tate duality. -/
@[simp↓]
theorem infiniteTateKerWeilPairing_kummerMap_kummerMap_eq_zero [DecidableEq w.Completion]
    (Q : W₂.toAffine.Point) (P : W₁.toAffine.Point) :
    have : CharZero w.Completion := (Completion.extensionEmbedding w).charZero
    φ.infiniteTateKerWeilPairing (φ.kummerMap Q) (φ.dual.kummerMap P) = 0 :=
  have : CharZero w.Completion := (Completion.extensionEmbedding w).charZero
  φ.tateKerWeilPairingOfH2MuHom_kummerMap_kummerMap_eq_zero (deg_isUnit φ)
    (infiniteH2MuToZMod w φ.degree) Q P

/-- Classes in the local Kummer subgroups of `φ` and `φ̂` at `w` pair to zero. -/
theorem infiniteTateKerWeilPairing_eq_zero_of_mem_range_kummerMap [DecidableEq w.Completion]
    {a : H1 (AbsoluteGaloisGroup w.Completion) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup w.Completion) (ofIsogeny φ.dual).KerCoeff} :
    have : CharZero w.Completion := (Completion.extensionEmbedding w).charZero
    a ∈ φ.kummerMap.range → b ∈ φ.dual.kummerMap.range → φ.infiniteTateKerWeilPairing a b = 0 :=
  have : CharZero w.Completion := (Completion.extensionEmbedding w).charZero
  φ.tateKerWeilPairingOfH2MuHom_eq_zero_of_mem_range_kummerMap (deg_isUnit φ)
    (infiniteH2MuToZMod w φ.degree)

/-- Classes in the Selmer local conditions of `φ` and `φ̂` at `w` pair to zero. -/
theorem infiniteTateKerWeilPairing_eq_zero_of_mem_ker
    {a : H1 (AbsoluteGaloisGroup w.Completion) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup w.Completion) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology).ker)
    (hb : b ∈ (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
      continuous_of_discreteTopology).ker) :
    φ.infiniteTateKerWeilPairing a b = 0 :=
  have := (Completion.extensionEmbedding w).charZero
  φ.tateKerWeilPairingOfH2MuHom_eq_zero_of_mem_ker (deg_isUnit φ) (infiniteH2MuToZMod w φ.degree)
    ha hb

/-- **Archimedean Euler characteristic:** `(deg φ)^w.mult · #H¹(K_w, E₁[φ]) = #E₁[φ] · #E₂[φ̂]`. -/
theorem degree_pow_mult_mul_natCard_H1_kerCoeff_completion [DecidableEq w.Completion] :
    φ.degree ^ w.mult * Nat.card (H1 (AbsoluteGaloisGroup w.Completion) (ofIsogeny φ).KerCoeff) =
      Nat.card (ofIsogeny φ).pointMapHom.ker * Nat.card (ofIsogeny φ.dual).pointMapHom.ker :=
  have := (Completion.extensionEmbedding w).charZero
  φ.degree_pow_mul_natCard_H1_kerCoeff_of_euler (deg_isUnit φ) (k := w.mult)
    (natCard_pow_mult_mul_natCard_H1_completion w (A := (ofIsogeny φ).KerCoeff) (n := φ.degree)
      φ.degree_nsmul_kerCoeff_eq_zero)

/-- At every infinite place `w`, `#H¹_φ(K_w) · #H¹_φ̂(K_w) = #H¹(K_w, E₁[φ])`. -/
theorem natCard_range_kummerMap_mul_dual_eq_natCard_H1_completion [DecidableEq w.Completion] :
    have : CharZero w.Completion := (Completion.extensionEmbedding w).charZero
    Nat.card φ.kummerMap.range * Nat.card φ.dual.kummerMap.range =
      Nat.card (H1 (AbsoluteGaloisGroup w.Completion) (ofIsogeny φ).KerCoeff) :=
  have : CharZero w.Completion := (Completion.extensionEmbedding w).charZero
  φ.natCard_range_kummerMap_mul_dual_eq_natCard_H1 <|
    φ.natCard_ker_kerCoeffIncl_mul_dual_eq_natCard_H1 (deg_isUnit φ) (k := w.mult)
      φ.degree_pow_mult_mul_natCard_H1_kerCoeff_completion
      φ.real_isogeny_index_or_subsingleton_completion

/-- **Local Kummer product:** `(deg φ)^w.mult · #H¹_φ(K_w) · #H¹_φ̂(K_w) = #E₁[φ] · #E₂[φ̂]`. -/
theorem degree_pow_mult_mul_natCard_range_kummerMap_mul_dual_completion
    [DecidableEq w.Completion] :
    have : CharZero w.Completion := (Completion.extensionEmbedding w).charZero
    φ.degree ^ w.mult * (Nat.card φ.kummerMap.range * Nat.card φ.dual.kummerMap.range) =
      Nat.card (ofIsogeny φ).pointMapHom.ker * Nat.card (ofIsogeny φ.dual).pointMapHom.ker :=
  have : CharZero w.Completion := (Completion.extensionEmbedding w).charZero
  (congrArg (φ.degree ^ w.mult * ·) φ.natCard_range_kummerMap_mul_dual_eq_natCard_H1_completion
    ).trans φ.degree_pow_mult_mul_natCard_H1_kerCoeff_completion

/-- **The Selmer local condition of `φ` at `w` is the exact annihilator of that of `φ̂`.** -/
theorem ker_kerCoeffIncl_eq_ker_infiniteTateKerWeilPairing :
    (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology).ker =
      (φ.infiniteTateKerWeilPairing.compl₂
        (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
          continuous_of_discreteTopology).ker.subtype).ker := by
  let : DecidableEq w.Completion := Classical.decEq w.Completion
  have := (Completion.extensionEmbedding w).charZero
  have := finite_galois_completion w
  exact φ.ker_kerCoeffIncl_eq_ker_tateKerWeilPairingOfH2MuHom (deg_isUnit φ)
    (infiniteH2MuToZMod w φ.degree) φ.infiniteTateKerWeilPairing_bijective
    (φ.natCard_ker_kerCoeffIncl_mul_dual_eq_natCard_H1 (deg_isUnit φ) (k := w.mult)
      φ.degree_pow_mult_mul_natCard_H1_kerCoeff_completion
      φ.real_isogeny_index_or_subsingleton_completion)

/-- **The local Kummer image of `φ` at `w` is the exact annihilator of that of `φ̂`.** -/
theorem range_kummerMap_eq_ker_infiniteTateKerWeilPairing [DecidableEq w.Completion] :
    have : CharZero w.Completion := (Completion.extensionEmbedding w).charZero
    φ.kummerMap.range =
      (φ.infiniteTateKerWeilPairing.compl₂ φ.dual.kummerMap.range.subtype).ker :=
  have : CharZero w.Completion := (Completion.extensionEmbedding w).charZero
  φ.range_kummerMap_eq_ker_compl₂ φ.infiniteTateKerWeilPairing
    φ.ker_kerCoeffIncl_eq_ker_infiniteTateKerWeilPairing

end InfinitePlace

end TauCeti.Isogeny

end
