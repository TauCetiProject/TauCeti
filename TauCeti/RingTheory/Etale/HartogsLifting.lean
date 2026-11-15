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
import TauCeti.Algebra.Algebra.Hom
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Lifting algebra maps from algebras étale over a punctured cover

Let `C` be an `A`-algebra and `a, b ∈ A` such that the localizations `C_a` and `C_b` are formally
étale over `A`. For instance, `C` may be the ring of sections of a finite étale cover of the
punctured spectrum of a local ring `A`, with `a, b` in the maximal ideal. Then `C` itself need not
be étale over `A`, but `A`-algebra maps from `C` still lift uniquely along nilpotent thickenings
`R → R ⧸ I` of any `A`-algebra `R` on which `a, b` is a weakly regular sequence, provided `a` is
also regular on `R ⧸ I`:

* over `D(a)` and over `D(b)` the map lifts uniquely, because `C_a` and `C_b` are formally étale;
* the two lifts agree over `D(ab)` by uniqueness;
* they glue to a map into `R` by the algebraic Hartogs principle: an element of `R_a` and an element
  of `R_b` with the same image in `R_{ab}` come from a unique element of `R`
  (`RingTheory.Sequence.IsWeaklyRegular.existsUnique_algebraMap_eq`);
* as `a` is regular on `R ⧸ I`, the map `R ⧸ I → R_a ⧸ I R_a` is injective, so the glued map
  reduces modulo `I` to the given map.

Passing to the limit, if `R` is `J`-adically complete and `a, b` is weakly regular on every
`R ⧸ J ^ (n + 1)`, then every `A`-algebra map `C → R ⧸ J` lifts uniquely to `C → R`.

This gives an algebraic route to the case of the local Lefschetz extension theorem (Stacks,
Lemma 58.20.7 (0BLM)) where `A` is complete along a nonzerodivisor `f` in its maximal ideal and
`A ⧸ f A` has depth at least two. Stacks proves 0BLM in general through full faithfulness of
restriction to the hypersurface section, which uses local cohomology and the theorem on formal
functions (Tags 0BM6 and 0EKS); in this case the elementary lifting above replaces that step.
Then `C` is the ring of sections of a finite étale cover `V` of the punctured spectrum `U` of `A`,
and `R` is a finite flat `A`-algebra with `J = f R`. A pair `a, b` in the maximal ideal which is
weakly regular on every `A ⧸ f ^ (n + 1) A` is, by flatness, weakly regular on every
`R ⧸ J ^ (n + 1)`. Morphisms over `U` into `V` from the part of `Spec (R ⧸ J ^ (n + 1))` over `U`
are then the `A`-algebra maps `C → R ⧸ J ^ (n + 1)`, so the theorem extends a morphism into `V`
from the part of the hypersurface section `f = 0` over `U` uniquely to the part of `Spec R` over
`U`.

## Main results

* `TauCeti.Algebra.existsUnique_lift_of_isUnit`: if `C_c` is formally étale over `A` for some
  `c : C`, then `A`-algebra maps `g : C → T ⧸ J` with `g c` a unit lift uniquely along nilpotent
  ideals `J`.
* `TauCeti.Algebra.existsUnique_lift_of_isWeaklyRegular`: if `C_a` and `C_b` are formally étale
  over `A` and `a, b` is weakly regular on `R`, then `A`-algebra maps `C → R ⧸ I` lift uniquely to
  `C → R` for every nilpotent ideal `I` with `a` regular on `R ⧸ I`.
* `TauCeti.Algebra.existsUnique_lift_of_isAdicComplete`: if `C_a` and `C_b` are formally étale
  over `A`, `R` is `J`-adically complete and `a, b` is weakly regular on `R ⧸ J ^ (n + 1)` for
  every `n`, then `A`-algebra maps `C → R ⧸ J` lift uniquely to `C → R`.

## References

* [Stacks Project, Lemma 58.20.7](https://stacks.math.columbia.edu/tag/0BLM), the local Lefschetz
  extension theorem.
* [Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I), extension of sections
  across a closed subset of depth at least two.
* The proof route (local lifts over `D(a)` and `D(b)` by formal étaleness, Hartogs gluing across
  the regular pair, and passage to the adic limit) follows T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Stacks/Purity/FormalEtaleLift.lean` (`exists_algHom_lift_of_regular_pair` and
  `exists_algHom_lift_of_isAdicComplete`), used there for the complete case of 0BLM in
  `lean/Pcf/Stacks/Purity/HypersurfaceLiftingComplete.lean`.
-/

public section

open RingTheory.Sequence

namespace TauCeti

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

namespace Algebra

variable {C : Type*} [CommRing C] [Algebra A C]

/-- **Lifting where `c` is a unit.** If `C_c` is formally étale over `A` for some `c : C`, then
every `A`-algebra map `g : C → T ⧸ J`, where `g c` is a unit and `J` is a nilpotent ideal, lifts
uniquely to an `A`-algebra map `C → T`. -/
theorem existsUnique_lift_of_isUnit (c : C) [Algebra.FormallyEtale A (Localization.Away c)]
    {T : Type*} [CommRing T] [Algebra A T] (J : Ideal T) (hJ : IsNilpotent J)
    (g : C →ₐ[A] T ⧸ J) (hc : IsUnit (g c)) :
    ∃! f : C →ₐ[A] T, (Ideal.Quotient.mkₐ A J).comp f = g := by
  let Cc := Localization.Away c
  let ι : C →ₐ[A] Cc := IsScalarTower.toAlgHom A C Cc
  -- Maps from `C` sending `c` to a unit factor through `C_c`.
  let g' : Cc →ₐ[A] T ⧸ J := IsLocalization.Away.liftAlgHom c (f := g) hc
  have hg' : g'.comp ι = g := AlgHom.ext fun x ↦ by simp [g', ι]
  refine ⟨(Algebra.FormallySmooth.lift J hJ g').comp ι, ?_, fun f hf ↦ ?_⟩
  · dsimp only
    rw [← AlgHom.comp_assoc, Algebra.FormallySmooth.comp_lift, hg']
  · -- Any lift sends `c` to a unit, as `J` is nilpotent, so it factors through `C_c` and is then
    -- determined, as `C_c` is formally unramified.
    have hfc : IsUnit (f c) := by
      rw [← hJ.isUnit_quotient_mk_iff, ← Ideal.Quotient.mkₐ_eq_mk A, ← AlgHom.comp_apply, hf]
      exact hc
    let f' : Cc →ₐ[A] T := IsLocalization.Away.liftAlgHom c (f := f) hfc
    have hf' : f'.comp ι = f := AlgHom.ext fun x ↦ by simp [f', ι]
    rw [← hf']
    congr 1
    refine Algebra.FormallyUnramified.lift_unique J hJ _ _ ?_
    rw [Algebra.FormallySmooth.comp_lift]
    have h : ((Ideal.Quotient.mkₐ A J).comp f').comp ι = g'.comp ι := by
      rw [AlgHom.comp_assoc, hf', hf, hg']
    exact IsLocalization.algHom_ext (Submonoid.powers c) h

/-- **Lifting over `D(x)`.** Let `ι : R → S` be an `A`-algebra map sending `x` to a unit. If
`C_x` is formally étale over `A` and `I` is a nilpotent ideal of `R`, then the image in `S ⧸ I S`
of an `A`-algebra map `g : C → R ⧸ I` lifts uniquely to an `A`-algebra map `C → S`. -/
private lemma existsUnique_lift_quotientMapₐ {x : A}
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A C x))] {S : Type*} [CommRing S]
    [Algebra A S] (ι : R →ₐ[A] S) (hx : IsUnit (ι (algebraMap A R x))) {I : Ideal R}
    (hI : IsNilpotent I) (g : C →ₐ[A] R ⧸ I) :
    ∃! f : C →ₐ[A] S, (Ideal.Quotient.mkₐ A (I.map ι)).comp f =
      (Ideal.quotientMapₐ (I.map ι) ι Ideal.le_comap_map).comp g :=
  existsUnique_lift_of_isUnit (algebraMap A C x) (I.map ι) (hI.map (Ideal.mapHom _)) _ (by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A S (S ⧸ _), ← ι.commutes]
    exact hx.map _)

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
    fa c ∈ Set.range (IsScalarTower.toAlgHom A R (Localization.Away (algebraMap A R a))) := by
  let Rb := Localization.Away (algebraMap A R b)
  let Rab := Localization.Away (algebraMap A R a * algebraMap A R b)
  let ιb : R →ₐ[A] Rb := IsScalarTower.toAlgHom A R Rb
  let ιab : R →ₐ[A] Rab := IsScalarTower.toAlgHom A R Rab
  -- `a` and `b` are units in `R_{ab}`, and `b` is a unit in `R_b`.
  have hua : IsUnit (ιab (algebraMap A R a)) :=
    IsLocalization.Away.isUnit_of_dvd (S := Rab) (algebraMap A R a * algebraMap A R b)
      (dvd_mul_right _ _)
  have hub : IsUnit (ιab (algebraMap A R b)) :=
    IsLocalization.Away.isUnit_of_dvd (S := Rab) (algebraMap A R a * algebraMap A R b)
      (dvd_mul_left _ _)
  -- The restriction maps `R_a → R_{ab}` and `R_b → R_{ab}`.
  let ρa : Localization.Away (algebraMap A R a) →ₐ[A] Rab :=
    IsLocalization.Away.liftAlgHom (algebraMap A R a) (f := ιab) hua
  let ρb : Rb →ₐ[A] Rab := IsLocalization.Away.liftAlgHom (algebraMap A R b) (f := ιab) hub
  have hρa : ρa.comp (IsScalarTower.toAlgHom A R _) = ιab := AlgHom.ext fun r ↦ by simp [ρa, ιab]
  have hρb : ρb.comp ιb = ιab := AlgHom.ext fun r ↦ by simp [ρb, ιb, ιab]
  -- Lift `g` over `D(b)`; the two lifts agree over `D(ab)`, so `fa c` and `fb c` glue.
  obtain ⟨fb, hfb, -⟩ := existsUnique_lift_quotientMapₐ (C := C) ιb
    (IsLocalization.Away.algebraMap_isUnit (algebraMap A R b)) hI g
  have hab : ρa.comp fa = ρb.comp fb :=
    (existsUnique_lift_quotientMapₐ (C := C) ιab hua hI g).unique
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
  -- Lift `g` over `D(a)`. As `a` is regular on `R`, the map `R → R_a` is injective, and the lift
  -- takes values in `R`, so it factors through a map `f : C → R`.
  obtain ⟨fa, hfa, hfa_uniq⟩ := existsUnique_lift_quotientMapₐ (C := C) ιa
    (IsLocalization.Away.algebraMap_isUnit (algebraMap A R a)) hI g
  have hιa : Function.Injective ιa := fun r s hrs ↦ by
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := .powers (algebraMap A R a)) hrs
    exact (ha.pow k) hk
  obtain ⟨f, hf⟩ : fa ∈ Set.range fun f : C →ₐ[A] R ↦ ιa.comp f := by
    rw [AlgHom.range_comp_left_of_injective ιa hιa]
    exact mem_range_of_lift_away hR' hI g fa hfa
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
    rw [← Ideal.map_pow, Ideal.zero_eq_bot]
    exact Ideal.map_quotient_self _⟩
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
