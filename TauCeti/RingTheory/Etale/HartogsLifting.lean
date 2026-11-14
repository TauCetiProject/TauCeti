/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Lifting algebra maps from algebras étale over a punctured cover

Let `C` be an `A`-algebra and `a, b ∈ A` such that the localizations `C_a` and `C_b` are formally
étale over `A`. For instance, `C` may be the ring of sections of a finite étale cover of the
punctured spectrum of a local ring `A`, with `a, b` in the maximal ideal. Then `C` itself need not
be étale over `A`, but `A`-algebra maps from `C` still lift uniquely along nilpotent thickenings of
any `A`-algebra `R` on which `a, b` is a weakly regular sequence:

* over `D(a)` and over `D(b)` the map lifts uniquely, because `C_a` and `C_b` are formally étale;
* the two lifts agree over `D(ab)` by uniqueness;
* they glue to a map into `R` by the algebraic Hartogs principle: an element of `R_a` and an element
  of `R_b` with the same image in `R_{ab}` come from a unique element of `R`
  (`RingTheory.Sequence.IsWeaklyRegular.existsUnique_algebraMap_eq`).

Passing to the limit, if `R` is `J`-adically complete and `a, b` is weakly regular on every
`R ⧸ J ^ (n + 1)`, then every `A`-algebra map `C → R ⧸ J` lifts uniquely to `C → R`.

This is the algebraic core of a step in the proof of the local Lefschetz extension theorem (Stacks,
Lemma 58.20.7 (0BLM)). There `C` is the ring of sections of a finite étale cover `V` of the
punctured spectrum `U` of a local ring `A`, and `R` is a finite flat `A`-algebra, complete along
`J = f R` for some `f ∈ A`, such that every `R ⧸ J ^ (n + 1)` has depth at least two at the closed
point. Morphisms over `U` into `V` from the part of `Spec (R ⧸ J ^ (n + 1))` over `U` are then
the `A`-algebra maps `C → R ⧸ J ^ (n + 1)`, so the theorem extends a morphism into `V` from the
part of the hypersurface section `f = 0` over `U` uniquely to the part of `Spec R` over `U`.

## Main results

* `TauCeti.Algebra.existsUnique_lift_of_isUnit`: if `C_a` is formally étale over `A`, then
  `A`-algebra maps from `C` into a ring in which `a` is a unit lift uniquely along nilpotent
  ideals.
* `TauCeti.Algebra.existsUnique_lift_of_isWeaklyRegular`: if `C_a` and `C_b` are formally étale
  over `A` and `a, b` is weakly regular on `R`, then `A`-algebra maps `C → R ⧸ I` lift uniquely to
  `C → R` for every nilpotent ideal `I` with `a` regular on `R ⧸ I`.
* `TauCeti.Algebra.existsUnique_lift_of_isAdicComplete`: the same for `R` complete along an ideal
  `J`, lifting maps `C → R ⧸ J`.

## References

* [Stacks Project, Lemma 58.20.7](https://stacks.math.columbia.edu/tag/0BLM), the local Lefschetz
  extension theorem.
* [Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I), extension of sections
  across a closed subset of depth at least two.
-/

public section

open RingTheory.Sequence

namespace TauCeti

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

namespace Algebra

variable {C : Type*} [CommRing C] [Algebra A C]

/-- **Lifting where `a` is a unit.** If `C_a` is formally étale over `A`, then every `A`-algebra
map `C → T ⧸ J`, where `a` is a unit in `T` and `J` is a nilpotent ideal, lifts uniquely to an
`A`-algebra map `C → T`. -/
theorem existsUnique_lift_of_isUnit (a : A)
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A C a))]
    {T : Type*} [CommRing T] [Algebra A T] (ha : IsUnit (algebraMap A T a))
    (J : Ideal T) (hJ : IsNilpotent J) (g : C →ₐ[A] T ⧸ J) :
    ∃! f : C →ₐ[A] T, (Ideal.Quotient.mkₐ A J).comp f = g := by
  let Ca := Localization.Away (algebraMap A C a)
  let ι : C →ₐ[A] Ca := IsScalarTower.toAlgHom A C Ca
  -- Maps from `C` into `A`-algebras in which `a` is a unit factor through `C_a`.
  have hJa : IsUnit (algebraMap A (T ⧸ J) a) := by
    rw [IsScalarTower.algebraMap_apply A T (T ⧸ J)]
    exact ha.map _
  let g' : Ca →ₐ[A] T ⧸ J :=
    IsLocalization.Away.liftAlgHom (algebraMap A C a) (f := g) (by rwa [AlgHom.commutes])
  have hg' : g'.comp ι = g := AlgHom.ext fun x ↦ by simp [g', ι]
  refine ⟨(Algebra.FormallySmooth.lift J hJ g').comp ι, ?_, fun f hf ↦ ?_⟩
  · dsimp only
    rw [← AlgHom.comp_assoc, Algebra.FormallySmooth.comp_lift, hg']
  · -- Any lift factors through `C_a` and is then determined, as `C_a` is formally unramified.
    let f' : Ca →ₐ[A] T :=
      IsLocalization.Away.liftAlgHom (algebraMap A C a) (f := f) (by rwa [AlgHom.commutes])
    have hf' : f'.comp ι = f := AlgHom.ext fun x ↦ by simp [f', ι]
    rw [← hf']
    congr 1
    refine Algebra.FormallyUnramified.lift_unique J hJ _ _ ?_
    rw [Algebra.FormallySmooth.comp_lift]
    have h : ((Ideal.Quotient.mkₐ A J).comp f').comp ι = g'.comp ι := by
      rw [AlgHom.comp_assoc, hf', hf, hg']
    exact IsLocalization.algHom_ext (Submonoid.powers (algebraMap A C a)) h

/-- Let `ι : R → S`, `ι' : R → S'` and `ρ : S → S'` be `A`-algebra maps with `ρ ∘ ι = ι'`. If
`f : C → S` lifts the image of `g : C → R ⧸ I` in `S ⧸ I S`, then `ρ ∘ f` lifts the image of `g`
in `S' ⧸ I S'`. -/
private lemma mkₐ_comp_comp_eq {S S' : Type*} [CommRing S] [CommRing S'] [Algebra A S]
    [Algebra A S'] {I : Ideal R} {ι : R →ₐ[A] S} {ι' : R →ₐ[A] S'} (ρ : S →ₐ[A] S')
    (hρ : ρ.comp ι = ι') {g : C →ₐ[A] R ⧸ I} {f : C →ₐ[A] S}
    (hf : (Ideal.Quotient.mkₐ A (I.map ι)).comp f =
      (Ideal.quotientMapₐ (I.map ι) ι Ideal.le_comap_map).comp g) :
    (Ideal.Quotient.mkₐ A (I.map ι')).comp (ρ.comp f) =
      (Ideal.quotientMapₐ (I.map ι') ι' Ideal.le_comap_map).comp g := by
  have hle : I.map ι ≤ (I.map ι').comap ρ := Ideal.map_le_iff_le_comap.2 fun r hr ↦ by
    rw [Ideal.mem_comap, Ideal.mem_comap, ← AlgHom.comp_apply, hρ]
    exact Ideal.mem_map_of_mem ι' hr
  rw [← AlgHom.comp_assoc, ← Ideal.quotient_map_comp_mkₐ _ _ hle, AlgHom.comp_assoc, hf,
    ← AlgHom.comp_assoc]
  congr 1
  refine Ideal.Quotient.algHom_ext A ?_
  rw [AlgHom.comp_assoc, Ideal.quotient_map_comp_mkₐ, ← AlgHom.comp_assoc,
    Ideal.quotient_map_comp_mkₐ, AlgHom.comp_assoc, hρ, Ideal.quotient_map_comp_mkₐ]

/-- The gluing step of `TauCeti.Algebra.existsUnique_lift_of_isWeaklyRegular`: a lift `fa` of `g`
over `D(a)` takes values in `R`. Indeed, `g` also lifts over `D(b)`, the two lifts agree over
`D(ab)` by uniqueness, and their values glue across the weakly regular sequence `a, b`. -/
private lemma mem_range_of_lift_away {a b : A}
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A C a))]
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A C b))]
    (hR : IsWeaklyRegular R [algebraMap A R a, algebraMap A R b]) {I : Ideal R}
    (hI : IsNilpotent I) (g : C →ₐ[A] R ⧸ I)
    (fa : C →ₐ[A] Localization.Away (algebraMap A R a))
    (hfa : (Ideal.Quotient.mkₐ A (I.map (IsScalarTower.toAlgHom A R _))).comp fa =
      (Ideal.quotientMapₐ _ (IsScalarTower.toAlgHom A R _) Ideal.le_comap_map).comp g) (c : C) :
    fa c ∈ (IsScalarTower.toAlgHom A R (Localization.Away (algebraMap A R a))).range := by
  let Rb := Localization.Away (algebraMap A R b)
  let Rab := Localization.Away (algebraMap A R a * algebraMap A R b)
  let ιb : R →ₐ[A] Rb := IsScalarTower.toAlgHom A R Rb
  let ιab : R →ₐ[A] Rab := IsScalarTower.toAlgHom A R Rab
  -- The restriction maps `R_a → R_{ab}` and `R_b → R_{ab}`.
  let ρa : Localization.Away (algebraMap A R a) →ₐ[A] Rab :=
    { IsLocalization.Away.awayToAwayRight (algebraMap A R a) (algebraMap A R b) (P := Rab) with
      commutes' := fun r ↦ by
        simp [IsScalarTower.algebraMap_apply A R (Localization.Away (algebraMap A R a)),
          IsScalarTower.algebraMap_apply A R Rab, IsLocalization.Away.awayToAwayRight_eq] }
  let ρb : Rb →ₐ[A] Rab :=
    { IsLocalization.Away.awayToAwayLeft (algebraMap A R b) (algebraMap A R a) (P := Rab) with
      commutes' := fun r ↦ by
        simp [IsScalarTower.algebraMap_apply A R Rb, IsScalarTower.algebraMap_apply A R Rab,
          IsLocalization.Away.awayToAwayLeft_eq] }
  have hρa : ρa.comp (IsScalarTower.toAlgHom A R _) = ιab :=
    AlgHom.ext fun r ↦ by simp [ρa, ιab, IsLocalization.Away.awayToAwayRight_eq]
  have hρb : ρb.comp ιb = ιab :=
    AlgHom.ext fun r ↦ by simp [ρb, ιb, ιab, IsLocalization.Away.awayToAwayLeft_eq]
  -- `b` is a unit in `R_b`, and `a` is a unit in `R_{ab}`.
  have hub : IsUnit (algebraMap A Rb b) := by
    rw [IsScalarTower.algebraMap_apply A R Rb]
    exact IsLocalization.Away.algebraMap_isUnit _
  have huab : IsUnit (algebraMap A Rab a) := by
    have hu := IsLocalization.Away.algebraMap_isUnit (S := Rab)
      (algebraMap A R a * algebraMap A R b)
    rw [map_mul] at hu
    rw [IsScalarTower.algebraMap_apply A R Rab]
    exact isUnit_of_mul_isUnit_left hu
  -- Lift `g` over `D(b)`; the two lifts agree over `D(ab)`, so `fa c` and `fb c` glue.
  obtain ⟨fb, hfb, -⟩ := existsUnique_lift_of_isUnit b hub (I.map ιb) (hI.map (Ideal.mapHom _))
    ((Ideal.quotientMapₐ (I.map ιb) ιb Ideal.le_comap_map).comp g)
  have hab : ρa.comp fa = ρb.comp fb :=
    (existsUnique_lift_of_isUnit a huab (I.map ιab) (hI.map (Ideal.mapHom _))
      ((Ideal.quotientMapₐ (I.map ιab) ιab Ideal.le_comap_map).comp g)).unique
      (mkₐ_comp_comp_eq ρa hρa hfa) (mkₐ_comp_comp_eq ρb hρb hfb)
  obtain ⟨r, ⟨hr, -⟩, -⟩ := hR.existsUnique_algebraMap_eq (fa c) (fb c) congr($hab c)
  exact ⟨r, hr⟩

/-- **Lifting across a weakly regular sequence.** Let `a, b ∈ A` be such that `C_a` and `C_b` are
formally étale over `A`, and let `R` be an `A`-algebra on which `a, b` is a weakly regular
sequence. If `I` is a nilpotent ideal of `R` with `a` regular on `R ⧸ I`, then every `A`-algebra
map `C → R ⧸ I` lifts uniquely to an `A`-algebra map `C → R`. -/
theorem existsUnique_lift_of_isWeaklyRegular {a b : A}
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A C a))]
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A C b))]
    (hR : IsWeaklyRegular R [a, b]) (I : Ideal R) (hI : IsNilpotent I)
    (haI : IsSMulRegular (R ⧸ I) a) (g : C →ₐ[A] R ⧸ I) :
    ∃! f : C →ₐ[A] R, (Ideal.Quotient.mkₐ A I).comp f = g := by
  have hR' : IsWeaklyRegular R [algebraMap A R a, algebraMap A R b] :=
    (isWeaklyRegular_map_algebraMap_iff R R [a, b]).2 hR
  have ha : IsSMulRegular R (algebraMap A R a) := ((isWeaklyRegular_cons_iff R _ _).1 hR').1
  let Ra := Localization.Away (algebraMap A R a)
  let ιa : R →ₐ[A] Ra := IsScalarTower.toAlgHom A R Ra
  let qa := Ideal.quotientMapₐ (I.map ιa) ιa Ideal.le_comap_map
  have hua : IsUnit (algebraMap A Ra a) := by
    rw [IsScalarTower.algebraMap_apply A R Ra]
    exact IsLocalization.Away.algebraMap_isUnit _
  -- Lift `g` over `D(a)`. As `a` is regular on `R`, the map `R → R_a` is injective, and the lift
  -- takes values in `R`, so it factors through a map `f : C → R`.
  obtain ⟨fa, hfa, hfa_uniq⟩ :=
    existsUnique_lift_of_isUnit a hua (I.map ιa) (hI.map (Ideal.mapHom _)) (qa.comp g)
  have hιa : Function.Injective ιa := fun r s hrs ↦ by
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := .powers (algebraMap A R a)) hrs
    exact (ha.pow k) hk
  have hrange := mem_range_of_lift_away hR' hI g fa hfa
  let e := AlgEquiv.ofInjective ιa hιa
  let f : C →ₐ[A] R := (e.symm : ιa.range →ₐ[A] R).comp (fa.codRestrict ιa.range hrange)
  have hf : ιa.comp f = fa := AlgHom.ext fun c ↦ by
    have := congrArg Subtype.val (e.apply_symm_apply ⟨fa c, hrange c⟩)
    rw [AlgEquiv.ofInjective_apply] at this
    exact this
  -- `R ⧸ I → R_a ⧸ I R_a` is injective since `a` is regular on `R ⧸ I`.
  have hqa : Function.Injective qa := by
    refine Ideal.quotientMap_injective' (H := Ideal.le_comap_map) fun r hr ↦ ?_
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (.powers (algebraMap A R a)) (S := Ra) I r).1 hr
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine (haI.pow k).right_eq_zero_of_smul ?_
    rwa [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨f, AlgHom.ext fun c ↦ hqa ?_, fun f' hf' ↦ ?_⟩
  · -- `f` lifts `g`, as its composite with `R → R_a` lifts the image of `g` in `R_a ⧸ I R_a`.
    have := congr($(hfa) c)
    rw [← hf, AlgHom.comp_apply, AlgHom.comp_apply] at this
    simpa [qa] using this
  · -- Another lift `f'` of `g` gives a lift `ιa ∘ f'` over `D(a)`, which is `fa = ιa ∘ f`.
    have hlift : (Ideal.Quotient.mkₐ A (I.map ιa)).comp (ιa.comp f') = qa.comp g := by
      rw [← hf', ← AlgHom.comp_assoc,
        ← Ideal.quotient_map_comp_mkₐ (I.map ιa) ιa Ideal.le_comap_map, AlgHom.comp_assoc]
    refine AlgHom.ext fun c ↦ hιa ?_
    have := congr($(hfa_uniq _ hlift) c)
    rw [← hf] at this
    exact this

/-- The finite levels of `TauCeti.Algebra.existsUnique_lift_of_isAdicComplete`: an `A`-algebra map
`C → R ⧸ J` lifts uniquely to `C → R ⧸ J ^ (n + 1)`, as `J ⧸ J ^ (n + 1)` is nilpotent. -/
private lemma existsUnique_lift_pow {a b : A}
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A C a))]
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A C b))]
    (J : Ideal R) (n : ℕ) (hR : IsWeaklyRegular (R ⧸ J ^ (n + 1)) [a, b])
    (hJ : IsSMulRegular (R ⧸ J) a) (g : C →ₐ[A] R ⧸ J) :
    ∃! f : C →ₐ[A] R ⧸ J ^ (n + 1),
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_self n.succ_ne_zero)).comp f = g := by
  have hle : J ^ (n + 1) ≤ J := Ideal.pow_le_self n.succ_ne_zero
  let K := J.map (Ideal.Quotient.mkₐ A (J ^ (n + 1)))
  -- `(R ⧸ J ^ (n + 1)) ⧸ K` is `R ⧸ J`, and `K` is nilpotent.
  let e := DoubleQuot.quotQuotEquivQuotOfLEₐ A hle
  have he := DoubleQuot.quotQuotEquivQuotOfLEₐ_comp_mkₐ A hle
  have hK : IsNilpotent K := ⟨n + 1, by
    rw [← Ideal.map_pow, Ideal.zero_eq_bot, eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro x hx
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hx⟩
  have haK : IsSMulRegular ((R ⧸ J ^ (n + 1)) ⧸ K) a :=
    (e.toLinearEquiv.isSMulRegular_congr a).2 hJ
  obtain ⟨f, hf, huniq⟩ :=
    existsUnique_lift_of_isWeaklyRegular hR K hK haK ((e.symm : R ⧸ J →ₐ[A] _).comp g)
  -- A map lifts `g` along `R ⧸ J ^ (n + 1) → R ⧸ J` iff it lifts `e⁻¹ ∘ g` modulo `K`.
  have key (f' : C →ₐ[A] R ⧸ J ^ (n + 1)) :
      (Ideal.Quotient.factorₐ A hle).comp f' = g ↔
        (Ideal.Quotient.mkₐ A K).comp f' = (e.symm : R ⧸ J →ₐ[A] _).comp g := by
    rw [← he, AlgHom.comp_assoc]
    constructor
    · rintro rfl
      rw [← AlgHom.comp_assoc, AlgEquiv.symm_comp, AlgHom.id_comp]
    · intro h
      rw [h, ← AlgHom.comp_assoc, AlgEquiv.comp_symm, AlgHom.id_comp]
  exact ⟨f, (key f).2 hf, fun f' hf' ↦ huniq f' ((key f').1 hf')⟩

/-- **Lifting to a complete algebra.** Let `a, b ∈ A` be such that `C_a` and `C_b` are formally
étale over `A`, and let `R` be an `A`-algebra which is complete along an ideal `J`, such that `a, b`
is a weakly regular sequence on `R ⧸ J ^ (n + 1)` for every `n`. Then every `A`-algebra map
`C → R ⧸ J` lifts uniquely to an `A`-algebra map `C → R`. -/
theorem existsUnique_lift_of_isAdicComplete {a b : A}
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A C a))]
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A C b))]
    (J : Ideal R) [IsAdicComplete J R] (hR : ∀ n, IsWeaklyRegular (R ⧸ J ^ (n + 1)) [a, b])
    (g : C →ₐ[A] R ⧸ J) :
    ∃! f : C →ₐ[A] R, (Ideal.Quotient.mkₐ A J).comp f = g := by
  have hJ : IsSMulRegular (R ⧸ J) a :=
    ((Ideal.quotientEquivAlgOfEq A (by rw [zero_add, pow_one] : J ^ (0 + 1) = J)).toLinearEquiv
      |>.isSMulRegular_congr a).1 ((isWeaklyRegular_cons_iff _ _ _).1 (hR 0)).1
  -- The unique lifts `F n : C → R ⧸ J ^ (n + 1)` are compatible.
  choose F hF hFuniq using fun n ↦ existsUnique_lift_pow J n (hR n) hJ g
  simp only at hF hFuniq
  have hcompat {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn))).comp (F n) =
        F m :=
    hFuniq m _ (by rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp, hF n])
  let G (n : ℕ) : C →ₐ[A] R ⧸ J ^ n :=
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right n.le_succ)).comp (F n)
  have hG {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp (G n) = G m := by
    simp only [G]
    rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp, ← hcompat hmn, ← AlgHom.comp_assoc,
      Ideal.Quotient.factorₐ_comp]
  refine ⟨IsAdicComplete.liftAlgHom J G hG, ?_, fun f hf ↦ ?_⟩
  · dsimp only
    rw [← Ideal.Quotient.factorₐ_comp_mk A (Ideal.pow_le_self one_ne_zero : J ^ 1 ≤ J),
      AlgHom.comp_assoc, IsAdicComplete.mkₐ_comp_liftAlgHom]
    simp only [G]
    rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp, hF 1]
  · refine IsAdicComplete.algHom_ext J fun n ↦ ?_
    rw [IsAdicComplete.mkₐ_comp_liftAlgHom]
    have hn : (Ideal.Quotient.mkₐ A (J ^ (n + 1))).comp f = F n :=
      hFuniq n _ (by rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp_mk, hf])
    rw [← Ideal.Quotient.factorₐ_comp_mk A
      (Ideal.pow_le_pow_right n.le_succ : J ^ (n + 1) ≤ J ^ n), AlgHom.comp_assoc, hn]

end Algebra

end TauCeti
