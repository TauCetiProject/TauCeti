/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.GaloisAction
import TauCeti.FieldTheory.FunctionField.Place.Extension.Decomposition
import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre

/-!
# Semilinear automorphisms of a Belyi pair and the stabilizer of a point

Let `X = (F, k(t) ↪ F)` be an algebraic Belyi pair over a field `k` of characteristic zero. A
**semilinear automorphism** of `X` is a pair `(φ, g)` of a ring automorphism `φ` of `F` and a
field automorphism `g` of `k` such that `φ` applies `g` to the coefficients of `k(t)`:
`φ (r(t)) = r^g(t)` for every rational function `r`. In particular `φ` fixes `t` and acts on the
constants by `g`. These form a subgroup `TauCeti.AlgebraicBelyiPair.semilinearAut X` of
`RingAut F × Aut(k)`, which acts on the places of `F` by transport.

A field automorphism `g` of `k` underlies a semilinear automorphism of `X` exactly when it
stabilizes the isomorphism class of `X`, because such a `φ` is the same thing as an isomorphism
of pairs from the conjugate `X^g` to `X`
(`TauCeti.AlgebraicBelyiPair.map_snd_semilinearAut`). For a place `P` of `F`, the
**pointed stabilizer** `U(X, P)` consists of those `g` that underlie a semilinear automorphism
fixing `P`. It is contained in the stabilizer `U(X)` of the class of `X`, whose fixed field is the
field of moduli `TauCeti.AlgebraicBelyiPair.IsoClass.fieldOfModuli`.

Two facts make `U(X, P)` usable for descent, in Köck's proof that a Belyi pair over `ℂ` is
defined over a finite extension of its field of moduli. If `P` lies over `t = q` for a rational
number `q`, every semilinear automorphism permutes the finitely many places over `t = q`, so
`U(X, P)` has finite index, at most the degree, in `U(X)`
(`TauCeti.AlgebraicBelyiPair.relIndex_pointedStabilizer_ne_zero`). If `P` lies over a point
other than `t = 0`, `t = 1`, `t = ∞` and has relative degree one over it, as is automatic over an
algebraically closed field, then the semilinear automorphism fixing `P` above a given `g` is
**unique**: two of them differ by an automorphism of `F` over `k(t)` fixing the unramified place
`P`, which is trivial (`TauCeti.Place.eq_one_of_smul_eq_self_of_ramificationIdx_eq_one`). Thus
`U(X, P)` acts on `F` by semilinear automorphisms fixing `t` and `P`
(`TauCeti.AlgebraicBelyiPair.pointedStabilizerEquiv`). In Köck's argument this action fixes a
generator of `F` over `k(t)` normalized by its Laurent expansion at `P` in `t - q`, so the
coefficients of its minimal polynomial over `k(t)` are fixed by `U(X, P)`.

## Main definitions

* `TauCeti.AlgebraicBelyiPair.semilinearAut`: the group of semilinear automorphisms of a pair,
  with its action on places.
* `TauCeti.AlgebraicBelyiPair.pointedStabilizer`: the automorphisms of `k` underlying a
  semilinear automorphism that fixes a given place.
* `TauCeti.AlgebraicBelyiPair.pointedStabilizerEquiv`: the identification of the stabilizer of
  an unramified place of relative degree one in the semilinear automorphism group with its
  pointed stabilizer.

## Main results

* `TauCeti.AlgebraicBelyiPair.map_snd_semilinearAut`: the automorphisms of `k` underlying
  semilinear automorphisms of `X` form the stabilizer of the class of `X`.
* `TauCeti.AlgebraicBelyiPair.pointedStabilizer_le_stabilizer`: `U(X, P) ≤ U(X)`.
* `TauCeti.AlgebraicBelyiPair.relIndex_pointedStabilizer_le_finrank` and
  `TauCeti.AlgebraicBelyiPair.relIndex_pointedStabilizer_ne_zero`: over a rational point the
  index of `U(X, P)` in `U(X)` is finite, at most the degree of `X`.
* `TauCeti.AlgebraicBelyiPair.eq_of_smul_eq_self_of_snd_eq`: over an unmarked point, a semilinear
  automorphism fixing a place of relative degree one is determined by its action on `k`.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  proof of (2.2) Theorem.
-/

public section

universe u

open Polynomial

namespace TauCeti

namespace AlgebraicBelyiPair

variable {k : Type u} [Field k] [CharZero k] (X : AlgebraicBelyiPair k)

/-! ### Semilinear automorphisms -/

/-- The identity automorphism of `k`, as a ring automorphism. -/
private theorem coe_one_algEquiv : ((1 : k ≃ₐ[ℚ] k) : k ≃+* k) = RingEquiv.refl k :=
  RingEquiv.ext fun _ ↦ AlgEquiv.one_apply (R := ℚ) _

/-- The **semilinear automorphisms** of an algebraic Belyi pair `X = (F, k(t) ↪ F)`: the pairs
`(φ, g)` of a ring automorphism `φ` of `F` and an automorphism `g` of `k` such that `φ` carries
each rational function `r` to `r` with `g` applied to its coefficients. In particular `φ` fixes
`t` and acts on the constants by `g`. -/
def semilinearAut : Subgroup (RingAut X × (k ≃ₐ[ℚ] k)) where
  carrier := {p | ∀ r : RatFunc k, p.1 (algebraMap (RatFunc k) X r) =
    algebraMap (RatFunc k) X (RatFunc.mapRingEquiv (p.2 : k ≃+* k) r)}
  mul_mem' {p q} hp hq r := by
    have hmul : ((p * q).2 : k ≃+* k) = (q.2 : k ≃+* k).trans p.2 := RingEquiv.ext fun _ ↦ by
      simp [AlgEquiv.mul_apply]
    rw [Prod.fst_mul, RingAut.mul_apply, hq, hp, hmul, RatFunc.mapRingEquiv_trans,
      RingEquiv.trans_apply]
  one_mem' r := by
    rw [Prod.fst_one, RingAut.one_apply, Prod.snd_one, coe_one_algEquiv,
      RatFunc.mapRingEquiv_refl, RingEquiv.refl_apply]
  inv_mem' {p} hp r := by
    have hinv : (p⁻¹.2 : k ≃+* k) = (p.2 : k ≃+* k).symm := by
      rw [Prod.snd_inv, AlgEquiv.aut_inv, AlgEquiv.toRingEquiv_symm]
    rw [Prod.fst_inv, RingAut.inv_apply, RingEquiv.symm_apply_eq, hp, hinv,
      ← RatFunc.mapRingEquiv_symm, RingEquiv.apply_symm_apply]

variable {X}

/-- Membership in the semilinear automorphisms of `X`. -/
theorem mem_semilinearAut_iff {p : RingAut X × (k ≃ₐ[ℚ] k)} :
    p ∈ semilinearAut X ↔ ∀ r : RatFunc k, p.1 (algebraMap (RatFunc k) X r) =
      algebraMap (RatFunc k) X (RatFunc.mapRingEquiv (p.2 : k ≃+* k) r) :=
  Iff.rfl

/-- A semilinear automorphism `(φ, g)` acts on the constants of `F` by `g`. -/
theorem apply_algebraMap_of_mem_semilinearAut {p : RingAut X × (k ≃ₐ[ℚ] k)}
    (hp : p ∈ semilinearAut X) (c : k) : p.1 (algebraMap k X c) = algebraMap k X (p.2 c) :=
  apply_algebraMap_eq_of_mapRingEquiv (p.2 : k ≃+* k) p.1 hp c

/-- **Semilinear automorphisms act on places**: `(φ, g)` carries a place `P` of `F` to the place
with valuation `v_P ∘ φ⁻¹`. -/
noncomputable instance : SMul (semilinearAut X) (Place k X) where
  smul p := Place.equivOfRingEquiv ((p : RingAut X × (k ≃ₐ[ℚ] k)).2 : k ≃+* k) p.1.1
    (apply_algebraMap_of_mem_semilinearAut p.2)

/-- The action of a semilinear automorphism `(φ, g)` on places is transport along `φ`. -/
theorem smul_def (p : semilinearAut X) (P : Place k X) :
    p • P = Place.equivOfRingEquiv ((p : RingAut X × (k ≃ₐ[ℚ] k)).2 : k ≃+* k) p.1.1
      (apply_algebraMap_of_mem_semilinearAut p.2) P :=
  (rfl)

/-- The valuation of the transported place `(φ, g) • P` is `v_P ∘ φ⁻¹`. -/
@[simp]
theorem valuation_smul (p : semilinearAut X) (P : Place k X) (z : X) :
    (p • P).valuation z = P.valuation ((p : RingAut X × (k ≃ₐ[ℚ] k)).1.symm z) := by
  rw [smul_def, Place.valuation_equivOfRingEquiv]

/-- **The action of semilinear automorphisms on places** is a group action. -/
noncomputable instance : MulAction (semilinearAut X) (Place k X) where
  one_smul P := Place.ext <| Valuation.ext fun _ ↦ by
    simp only [valuation_smul, OneMemClass.coe_one, Prod.fst_one, ← RingAut.inv_apply, inv_one,
      RingAut.one_apply]
  mul_smul _ _ _ := Place.ext <| Valuation.ext fun _ ↦ by
    simp only [valuation_smul, Subgroup.coe_mul, Prod.fst_mul, ← RingAut.inv_apply, mul_inv_rev,
      RingAut.mul_apply]

/-- A semilinear automorphism fixes a place `P` exactly when it preserves the valuation of `P`. -/
theorem smul_eq_self_iff_valuation_apply_eq {p : semilinearAut X} {P : Place k X} :
    p • P = P ↔ ∀ z : X, P.valuation ((p : RingAut X × (k ≃ₐ[ℚ] k)).1 z) = P.valuation z := by
  refine ⟨fun h z ↦ ?_, fun h ↦ Place.ext <| Valuation.ext fun z ↦ ?_⟩
  · conv_lhs => rw [← h]
    rw [valuation_smul, RingEquiv.symm_apply_apply]
  · rw [valuation_smul, ← h, RingEquiv.apply_symm_apply]

/-- A semilinear automorphism `(φ, g)` carries the places of `F` over a place `Q` of `k(t)` to the
places over the conjugate of `Q` along `g`. -/
theorem restrict_smul (p : semilinearAut X) (P : Place k X) :
    (p • P).restrict k (RatFunc k) =
      Place.equivOfRingEquiv ((p : RingAut X × (k ≃ₐ[ℚ] k)).2 : k ≃+* k)
        (RatFunc.mapRingEquiv ((p : RingAut X × (k ≃ₐ[ℚ] k)).2 : k ≃+* k))
        (RatFunc.mapRingEquiv_algebraMap_const _) (P.restrict k (RatFunc k)) := by
  rw [smul_def]
  exact Place.restrict_equivOfRingEquiv _ _ _ _ p.2 _ P

variable (X) in
/-- **The automorphisms of `k` underlying semilinear automorphisms of `X` form the stabilizer of
the isomorphism class of `X`**: a `g`-semilinear automorphism of `F` fixing `t` is the same thing
as an isomorphism from the conjugate pair `X^g` to `X`. -/
theorem map_snd_semilinearAut :
    (semilinearAut X).map (MonoidHom.snd _ _) =
      MulAction.stabilizer (k ≃ₐ[ℚ] k) (IsoClass.mk X) := by
  ext g
  rw [Subgroup.mem_map, MulAction.mem_stabilizer_iff, IsoClass.smul_mk_eq_mk_iff]
  constructor
  · rintro ⟨p, hp, hpg⟩
    rw [MonoidHom.coe_snd] at hpg
    subst hpg
    -- The isomorphism `X^g ≅ X` is `φ`, read on the underlying field of the conjugate.
    refine ⟨AlgEquiv.ofRingEquiv (f := (conjRingEquiv (p.2 : k ≃+* k) X).symm.trans p.1)
      fun r ↦ ?_⟩
    rw [RingEquiv.trans_apply, algebraMap_conj, RingEquiv.symm_apply_apply, hp,
      ← RatFunc.mapRingEquiv_symm, RingEquiv.apply_symm_apply]
  · rintro ⟨e⟩
    refine ⟨((conjRingEquiv (g : k ≃+* k) X).trans e.toRingEquiv, g), fun r ↦ ?_, rfl⟩
    rw [RingEquiv.trans_apply, conjRingEquiv_algebraMap_ratFunc, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.commutes]

/-! ### The pointed stabilizer -/

variable (X) in
/-- The **pointed stabilizer** `U(X, P)` of a place `P` of an algebraic Belyi pair `X`: the
automorphisms `g` of `k` for which some `g`-semilinear automorphism of `X` fixes `P`. In Köck's
notation, for `X = (F, t)` and `P` a point over an unbranched value `Q`, this is the group
`U(F, t, P)` of those `g` admitting an isomorphism of pairs `f_g : X^g ≅ X` with
`f_g(P^g) = P`. -/
noncomputable def pointedStabilizer (P : Place k X) : Subgroup (k ≃ₐ[ℚ] k) :=
  (MulAction.stabilizer (semilinearAut X) P).map
    ((MonoidHom.snd _ _).comp (semilinearAut X).subtype)

/-- An automorphism `g` of `k` lies in the pointed stabilizer of `P` exactly when some
`g`-semilinear automorphism of `F` preserves the valuation of `P`. -/
theorem mem_pointedStabilizer_iff {P : Place k X} {g : k ≃ₐ[ℚ] k} :
    g ∈ pointedStabilizer X P ↔ ∃ φ : RingAut X,
      (∀ r : RatFunc k, φ (algebraMap (RatFunc k) X r) =
        algebraMap (RatFunc k) X (RatFunc.mapRingEquiv (g : k ≃+* k) r)) ∧
      ∀ z : X, P.valuation (φ z) = P.valuation z := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p : RingAut X × (k ≃ₐ[ℚ] k)).1, p.2, smul_eq_self_iff_valuation_apply_eq.mp hp⟩
  · rintro ⟨φ, hφ, hφP⟩
    exact ⟨⟨(φ, g), hφ⟩, smul_eq_self_iff_valuation_apply_eq.mpr hφP, rfl⟩

/-- **`U(X, P) ≤ U(X)`**: an automorphism of `k` in the pointed stabilizer of a place stabilizes
the isomorphism class of the pair. -/
theorem pointedStabilizer_le_stabilizer (P : Place k X) :
    pointedStabilizer X P ≤ MulAction.stabilizer (k ≃ₐ[ℚ] k) (IsoClass.mk X) := by
  rw [← map_snd_semilinearAut, pointedStabilizer, ← Subgroup.map_map]
  exact Subgroup.map_mono (Subgroup.map_subtype_le _)

/-- The index of `U(X, P)` in `U(X)` divides that of the stabilizer of `P` in the semilinear
automorphism group, which maps onto `U(X)` carrying the stabilizer of `P` onto `U(X, P)`. -/
private theorem relIndex_pointedStabilizer_dvd_index (P : Place k X) :
    (pointedStabilizer X P).relIndex (MulAction.stabilizer (k ≃ₐ[ℚ] k) (IsoClass.mk X)) ∣
      (MulAction.stabilizer (semilinearAut X) P).index := by
  have hrange : (⊤ : Subgroup (semilinearAut X)).map
      ((MonoidHom.snd _ _).comp (semilinearAut X).subtype) =
      MulAction.stabilizer (k ≃ₐ[ℚ] k) (IsoClass.mk X) := by
    rw [← map_snd_semilinearAut, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [pointedStabilizer, ← hrange, Subgroup.relIndex_map_map, top_sup_eq,
    Subgroup.relIndex_top_right]
  exact Subgroup.index_dvd_of_le le_sup_left

/-- Over a rational point, the orbit of `P` under the semilinear automorphisms lies in the finite
fibre over that point, so the stabilizer of `P` has nonzero index at most the degree. -/
private theorem index_stabilizer_pos_and_le_finrank {P : Place k X} {q : ℚ}
    (hP : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k))) :
    0 < (MulAction.stabilizer (semilinearAut X) P).index ∧
      (MulAction.stabilizer (semilinearAut X) P).index ≤ Module.finrank (RatFunc k) X := by
  have hfin := Place.finite_setOf_restrict_eq (k' := k) (F' := X) k (RatFunc k)
    (P.restrict k (RatFunc k))
  have horbit : MulAction.orbit (semilinearAut X) P ⊆
      {P' : Place k X | P'.restrict k (RatFunc k) = P.restrict k (RatFunc k)} := by
    rintro _ ⟨p, rfl⟩
    rw [Set.mem_ofPred_eq, restrict_smul, hP,
      Place.equivOfRingEquiv_mapRingEquiv_adicOfIrreducible_X_sub_C, map_ratCast]
  rw [MulAction.index_stabilizer]
  exact ⟨(Set.ncard_pos (hfin.subset horbit)).mpr ⟨P, MulAction.mem_orbit_self P⟩,
    (Set.ncard_le_ncard horbit hfin).trans (Place.ncard_setOf_restrict_eq_le_finrank k _ _)⟩

/-- **The pointed stabilizer of a point over `t = q`, for rational `q`, has index at most the
degree in the stabilizer of the class.** Semilinear automorphisms fix the rational place `t = q`
of `k(t)`, so they permute the places of `F` over it, of which there are at most `[F : k(t)]`. -/
theorem relIndex_pointedStabilizer_le_finrank {P : Place k X} {q : ℚ}
    (hP : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k))) :
    (pointedStabilizer X P).relIndex (MulAction.stabilizer (k ≃ₐ[ℚ] k) (IsoClass.mk X)) ≤
      Module.finrank (RatFunc k) X :=
  have h := index_stabilizer_pos_and_le_finrank hP
  (Nat.le_of_dvd h.1 (relIndex_pointedStabilizer_dvd_index P)).trans h.2

/-- **The pointed stabilizer of a point over `t = q`, for rational `q`, has finite index in the
stabilizer of the class.** So its fixed field is a finite extension of the field of moduli. -/
theorem relIndex_pointedStabilizer_ne_zero {P : Place k X} {q : ℚ}
    (hP : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k))) :
    (pointedStabilizer X P).relIndex (MulAction.stabilizer (k ≃ₐ[ℚ] k) (IsoClass.mk X)) ≠ 0 :=
  ne_zero_of_dvd_ne_zero (index_stabilizer_pos_and_le_finrank hP).1.ne'
    (relIndex_pointedStabilizer_dvd_index P)

/-! ### Uniqueness over an unmarked point -/

section Unmarked

variable {P : Place k X} (hP : P.restrict k (RatFunc k) ∉ Place.zeroOneInfty k)
  (hf : Place.relativeDegree k (RatFunc k) P = 1)

include hP hf

/-- A semilinear automorphism acting trivially on `k` and fixing an unmarked place of relative
degree one is the identity: it is an automorphism of `F` over `k(t)` fixing an unramified place
of relative degree one. -/
private theorem eq_one_of_smul_eq_self_of_snd_eq_one {p : semilinearAut X} (hp : p • P = P)
    (h1 : (p : RingAut X × (k ≃ₐ[ℚ] k)).2 = 1) : p = 1 := by
  obtain ⟨⟨φ, g⟩, hφ⟩ := p
  obtain rfl : g = 1 := h1
  let σ : X ≃ₐ[RatFunc k] X := AlgEquiv.ofRingEquiv (f := φ) fun r ↦ by
    rw [hφ r, coe_one_algEquiv, RatFunc.mapRingEquiv_refl, RingEquiv.refl_apply]
  have hσP : σ • P = P := Place.ext <| Valuation.ext fun z ↦ by
    rw [Place.valuation_smul, ← smul_eq_self_iff_valuation_apply_eq.mp hp (σ.symm z)]
    exact congrArg P.valuation (σ.apply_symm_apply z)
  have hσ := Place.eq_one_of_smul_eq_self_of_ramificationIdx_eq_one hσP
    (X.isAlgebraicBelyiPair.ramificationIdx_eq_one hP) hf
  exact Subtype.ext <| Prod.ext (RingEquiv.ext fun x ↦ DFunLike.congr_fun hσ x) rfl

/-- **A semilinear automorphism fixing an unmarked place of relative degree one is determined by
its action on the constants.** If two semilinear automorphisms `(φ, g)` and `(ψ, g)` fix a place
`P` lying over a place of `k(t)` other than `t = 0`, `t = 1`, `t = ∞`, with relative degree one,
then `φ = ψ`: the automorphism `ψ⁻¹ φ` of `F` over `k(t)` fixes the unramified place `P`. -/
theorem eq_of_smul_eq_self_of_snd_eq {p p' : semilinearAut X} (hp : p • P = P) (hp' : p' • P = P)
    (h : (p : RingAut X × (k ≃ₐ[ℚ] k)).2 = (p' : RingAut X × (k ≃ₐ[ℚ] k)).2) : p = p' := by
  refine (inv_mul_eq_one.mp (eq_one_of_smul_eq_self_of_snd_eq_one hP hf ?_ ?_)).symm
  · rw [mul_smul, hp, inv_smul_eq_iff, hp']
  · rw [Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv, h, inv_mul_cancel]

/-- **The semilinear action of the pointed stabilizer.** At a place `P` over an unmarked point,
with relative degree one, the stabilizer of `P` in the semilinear automorphism group maps
isomorphically onto `U(X, P)`. Its inverse lets each `g ∈ U(X, P)` act on `F` by the unique
`g`-semilinear automorphism fixing `t` and `P`. -/
noncomputable def pointedStabilizerEquiv :
    MulAction.stabilizer (semilinearAut X) P ≃* pointedStabilizer X P :=
  (MonoidHom.ofInjective (f := ((MonoidHom.snd _ _).comp (semilinearAut X).subtype).comp
    (MulAction.stabilizer (semilinearAut X) P).subtype) fun p p' h ↦
      Subtype.ext (eq_of_smul_eq_self_of_snd_eq hP hf p.2 p'.2 h)).trans
    (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, pointedStabilizer]))

/-- The pointed stabilizer equivalence remembers the action on `k`. -/
@[simp]
theorem coe_pointedStabilizerEquiv_apply (p : MulAction.stabilizer (semilinearAut X) P) :
    (pointedStabilizerEquiv hP hf p : k ≃ₐ[ℚ] k) =
      ((p : semilinearAut X) : RingAut X × (k ≃ₐ[ℚ] k)).2 :=
  (rfl)

/-- The semilinear automorphism attached to `g ∈ U(X, P)` acts on `k` by `g`. -/
@[simp]
theorem snd_pointedStabilizerEquiv_symm_apply (g : pointedStabilizer X P) :
    (((pointedStabilizerEquiv hP hf).symm g : semilinearAut X) : RingAut X × (k ≃ₐ[ℚ] k)).2 =
      g := by
  rw [← coe_pointedStabilizerEquiv_apply hP hf, MulEquiv.apply_symm_apply]

end Unmarked

end AlgebraicBelyiPair

end TauCeti
