/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Free.Enveloping
public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion
public import TauCeti.RingTheory.Nilpotent.BCH

import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Embedding

/-!
# The universal Baker–Campbell–Hausdorff element

Let `F` be the free Lie algebra over `ℚ` on a type `S`, and let `J` be the augmentation ideal of
its universal enveloping algebra `U(F)`. Since the word-length filtration of `U(F)` coincides with
the powers of `J` (`TauCeti.FreeLieAlgebra.degreeFiltration_eq_augmentation_pow`), the completed
bialgebra exponential and logarithm identify `log (exp (ι x) * exp (ι y))` in every truncated
enveloping algebra `U(F) ⧸ J ^ (c + 1)` with the image of a Lie element of `F`
(`TauCeti.FreeLieAlgebra.exists_log_exp_mul_exp`,
`TauCeti.FreeLieAlgebra.exists_exp_eq_exp_mul_exp`).

Because the canonical map `ι : F → U(F)` is injective over `ℚ`, the induced Lie homomorphism
`TauCeti.UniversalEnvelopingAlgebra.lowerCentralQuotientι` from the free nilpotent quotient
`F ⧸ lowerCentralSeries c` to `U(F) ⧸ J ^ (c + 1)` is injective
(`TauCeti.FreeLieAlgebra.lowerCentralQuotientι_injective`). Combining existence and injectivity
determines a unique class in `F ⧸ lowerCentralSeries c` whose exponential is
`exp (ι x) * exp (ι y)` (`TauCeti.FreeLieAlgebra.existsUnique_lowerCentralQuotient_exp_eq`).

For `S = Fin 2` with generators `X = of 0` and `Y = of 1`, this unique class is the universal
Baker–Campbell–Hausdorff element `TauCeti.FreeLieAlgebra.bchElement c` of nilpotency class `c`.
These classes form a compatible system under the lower-central transitions
(`TauCeti.FreeLieAlgebra.factor_bchElement`), establish
`TauCeti.FreeLieAlgebra.exists_bch_exp_mul_exp`, and agree with the explicit
Baker–Campbell–Hausdorff polynomials in classes `0`, `1`, `2`, and `3`.

## Main definitions

* `TauCeti.FreeLieAlgebra.bchElement`: the unique class in the free nilpotent Lie algebra on two
  generators of class `c` whose exponential in `U(F) ⧸ J ^ (c + 1)` equals
  `exp (ι X) * exp (ι Y)`.

## Main results

* `TauCeti.FreeLieAlgebra.exists_log_exp_mul_exp` and
  `TauCeti.FreeLieAlgebra.exists_exp_eq_exp_mul_exp`: existence of a Lie preimage of
  `log (exp (ι x) * exp (ι y))` in `U(F) ⧸ J ^ (c + 1)` for any free rational Lie algebra.
* `TauCeti.FreeLieAlgebra.existsUnique_lowerCentralQuotient_exp_eq`: existence and uniqueness in
  the nilpotent quotient `F ⧸ lowerCentralSeries c`.
* `TauCeti.FreeLieAlgebra.exp_lowerCentralQuotientι_bchElement` and
  `TauCeti.FreeLieAlgebra.lowerCentralQuotientι_bchElement`: defining exponential and logarithm
  equations for `bchElement`.
* `TauCeti.FreeLieAlgebra.factor_bchElement`: compatibility of `bchElement` across nilpotency
  classes.
* `TauCeti.FreeLieAlgebra.exists_bch_exp_mul_exp`: existence of a representative `b` in the free
  Lie algebra on two generators satisfying `exp (ι b) = exp (ι X) * exp (ι Y)` modulo `J ^ (c + 1)`.
* `TauCeti.FreeLieAlgebra.bchElement_zero`, `bchElement_one`, `bchElement_two`, and
  `bchElement_three`: explicit evaluations of `bchElement` through class three.
-/

public section

namespace TauCeti.FreeLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section General

variable {S : Type*}

local notation "F" => _root_.FreeLieAlgebra ℚ S
local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ F
local notation "J" => HopfIdeal.toIdeal (HopfIdeal.augmentation ℚ U)

private theorem free_degree_nonpos_eq_bot (n : ℕ)
    (hn : (Nat.castAddMonoidHom ℤ) n ≤ 0) : homogeneousSubmodule ℚ S n = ⊥ := by
  obtain rfl : n = 0 := by simpa using hn
  exact homogeneousSubmodule_zero ℚ S

/-- In the truncated enveloping algebra `U(F) ⧸ J ^ (c + 1)` of a free rational Lie algebra,
`log (exp (ι x) * exp (ι y))` is represented by a Lie element. -/
theorem exists_log_exp_mul_exp (x y : F) (c : ℕ) :
    ∃ b : F,
      Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ b) =
        IsNilpotent.log
          (IsNilpotent.exp
              (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) *
            IsNilpotent.exp
              (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ y))) := by
  suffices ∀ (I : Ideal U) [I.IsTwoSided],
      (UniversalEnvelopingAlgebra.degreeFiltration (homogeneousSubmodule ℚ S)
        (Nat.castAddMonoidHom ℤ) (fun n hn => free_degree_nonpos_eq_bot n hn.le)).ideal (c + 1) =
        I →
      ∃ b : F, Ideal.Quotient.mk I (_root_.UniversalEnvelopingAlgebra.ι ℚ b) =
        IsNilpotent.log
          (IsNilpotent.exp (Ideal.Quotient.mk I (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) *
            IsNilpotent.exp (Ideal.Quotient.mk I (_root_.UniversalEnvelopingAlgebra.ι ℚ y))) from
    this (J ^ (c + 1)) (degreeFiltration_eq_augmentation_pow ℚ S (c + 1))
  rintro I _ rfl
  exact UniversalEnvelopingAlgebra.exists_log_exp_mul_exp_degreeFiltration
    (homogeneousSubmodule ℚ S) (Nat.castAddMonoidHom ℤ) free_degree_nonpos_eq_bot x y c

/-- In the truncated enveloping algebra `U(F) ⧸ J ^ (c + 1)` of a free rational Lie algebra,
the product `exp (ι x) * exp (ι y)` is the exponential of a Lie element. -/
theorem exists_exp_eq_exp_mul_exp (x y : F) (c : ℕ) :
    ∃ b : F,
      IsNilpotent.exp
          (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ b)) =
        IsNilpotent.exp
            (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) *
          IsNilpotent.exp
            (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) := by
  suffices ∀ (I : Ideal U) [I.IsTwoSided],
      (UniversalEnvelopingAlgebra.degreeFiltration (homogeneousSubmodule ℚ S)
        (Nat.castAddMonoidHom ℤ) (fun n hn => free_degree_nonpos_eq_bot n hn.le)).ideal (c + 1) =
        I →
      ∃ b : F, IsNilpotent.exp (Ideal.Quotient.mk I (_root_.UniversalEnvelopingAlgebra.ι ℚ b)) =
        IsNilpotent.exp (Ideal.Quotient.mk I (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) *
          IsNilpotent.exp (Ideal.Quotient.mk I (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) from
    this (J ^ (c + 1)) (degreeFiltration_eq_augmentation_pow ℚ S (c + 1))
  rintro I _ rfl
  exact UniversalEnvelopingAlgebra.exists_exp_eq_exp_mul_exp_degreeFiltration
    (homogeneousSubmodule ℚ S) (Nat.castAddMonoidHom ℤ) free_degree_nonpos_eq_bot x y c

/-- In the free nilpotent Lie algebra `F ⧸ lowerCentralSeries c` over `ℚ`, there is a unique class
whose image under `lowerCentralQuotientι` has exponential `exp (ι x) * exp (ι y)`. -/
theorem existsUnique_lowerCentralQuotient_exp_eq (x y : F) (c : ℕ) :
    ∃! z : F ⧸ LieModule.lowerCentralSeries ℚ F F c,
      IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c z) =
        IsNilpotent.exp
            (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) *
          IsNilpotent.exp
            (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) := by
  obtain ⟨b, hb⟩ := exists_exp_eq_exp_mul_exp x y c
  have hb' : IsNilpotent.exp
      (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F c (LieSubmodule.Quotient.mk b)) =
      IsNilpotent.exp
          (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) *
        IsNilpotent.exp
          (Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) := by
    simpa only [UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using hb
  refine ⟨LieSubmodule.Quotient.mk b, hb', fun z hz => ?_⟩
  apply lowerCentralQuotientι_injective ℚ S (UniversalEnvelopingAlgebra.ι_injective ℚ F) c
  have hlog := congrArg IsNilpotent.log (hz.trans hb'.symm)
  rwa [IsNilpotent.log_exp (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c z),
    IsNilpotent.log_exp
      (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F c _)] at hlog

end General

section Universal

local notation "F₂" => _root_.FreeLieAlgebra ℚ (Fin 2)
local notation "U₂" => _root_.UniversalEnvelopingAlgebra ℚ F₂
local notation "J₂" => HopfIdeal.toIdeal (HopfIdeal.augmentation ℚ U₂)

/-- The universal Baker–Campbell–Hausdorff element of nilpotency class `c`: the unique class in
the free nilpotent Lie algebra on two generators `X = of 0` and `Y = of 1` whose image in
`U(F₂) ⧸ J₂ ^ (c + 1)` satisfies `exp (ι bch) = exp (ι X) * exp (ι Y)`. -/
noncomputable def bchElement (c : ℕ) :
    F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ c :=
  (existsUnique_lowerCentralQuotient_exp_eq
    (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2))
    (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)) c).choose

/-- The exponential of `bchElement c` in `U(F₂) ⧸ J₂ ^ (c + 1)` is `exp (ι X) * exp (ι Y)`. -/
theorem exp_lowerCentralQuotientι_bchElement (c : ℕ) :
    IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c (bchElement c)) =
      IsNilpotent.exp
          (Ideal.Quotient.mk (J₂ ^ (c + 1))
            (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) *
        IsNilpotent.exp
          (Ideal.Quotient.mk (J₂ ^ (c + 1))
            (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))) :=
  (existsUnique_lowerCentralQuotient_exp_eq
    (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2))
    (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)) c).choose_spec.1

/-- The image of `bchElement c` in `U(F₂) ⧸ J₂ ^ (c + 1)` is `log (exp (ι X) * exp (ι Y))`. -/
theorem lowerCentralQuotientι_bchElement (c : ℕ) :
    UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c (bchElement c) =
      IsNilpotent.log
        (IsNilpotent.exp
            (Ideal.Quotient.mk (J₂ ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) *
          IsNilpotent.exp
            (Ideal.Quotient.mk (J₂ ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ
                (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2))))) := by
  rw [← exp_lowerCentralQuotientι_bchElement c,
    IsNilpotent.log_exp
      (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F₂ c (bchElement c))]

/-- Uniqueness of `bchElement c` from the exponential identity. -/
theorem eq_bchElement_of_exp_eq (c : ℕ)
    {z : F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ c}
    (hz : IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c z) =
      IsNilpotent.exp
          (Ideal.Quotient.mk (J₂ ^ (c + 1))
            (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) *
        IsNilpotent.exp
          (Ideal.Quotient.mk (J₂ ^ (c + 1))
            (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2))))) :
    z = bchElement c :=
  (existsUnique_lowerCentralQuotient_exp_eq
    (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2))
    (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)) c).choose_spec.2 z hz

/-- Uniqueness of `bchElement c` from the logarithm identity. -/
theorem eq_bchElement_of_lowerCentralQuotientι_eq (c : ℕ)
    {z : F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ c}
    (hz : UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ F₂ c z =
      IsNilpotent.log
        (IsNilpotent.exp
            (Ideal.Quotient.mk (J₂ ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) *
          IsNilpotent.exp
            (Ideal.Quotient.mk (J₂ ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ
                (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))))) :
    z = bchElement c :=
  lowerCentralQuotientι_injective ℚ (Fin 2) (UniversalEnvelopingAlgebra.ι_injective ℚ F₂) c
    (hz.trans (lowerCentralQuotientι_bchElement c).symm)

/-- The universal Baker–Campbell–Hausdorff elements are compatible across nilpotency classes. -/
theorem factor_bchElement {c d : ℕ} (h : c ≤ d) :
    LieIdeal.factor (LieModule.antitone_lowerCentralSeries ℚ F₂ F₂ h) (bchElement d) =
      bchElement c := by
  apply eq_bchElement_of_exp_eq c
  have hf := Ideal.Quotient.factor_mk
    (Ideal.pow_le_pow_right (I := J₂) (Nat.add_le_add_right h 1))
  rw [UniversalEnvelopingAlgebra.lowerCentralQuotientι_factor ℚ F₂ h,
    ← (UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F₂ d
      (bchElement d)).map_exp,
    exp_lowerCentralQuotientι_bchElement d, map_mul]
  have hx : IsNilpotent (Ideal.Quotient.mk (J₂ ^ (d + 1))
      (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) := by
    simpa only [UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
      UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F₂ d
        (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))
  have hy : IsNilpotent (Ideal.Quotient.mk (J₂ ^ (d + 1))
      (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))) := by
    simpa only [UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] using
      UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ F₂ d
        (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))
  rw [hx.map_exp, hy.map_exp, hf, hf]

/-- **Existence of the universal Baker–Campbell–Hausdorff element of class `c`.** In the truncated
enveloping algebra `U(F₂) ⧸ J₂ ^ (c + 1)` of the free rational Lie algebra on two generators, there
exists `b` such that `exp (ι b) = exp (ι X) * exp (ι Y)`. -/
theorem exists_bch_exp_mul_exp (c : ℕ) :
    ∃ b : F₂,
      IsNilpotent.exp
          (Ideal.Quotient.mk (J₂ ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ b)) =
        IsNilpotent.exp
            (Ideal.Quotient.mk (J₂ ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) *
          IsNilpotent.exp
            (Ideal.Quotient.mk (J₂ ^ (c + 1))
              (_root_.UniversalEnvelopingAlgebra.ι ℚ (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))) :=
  exists_exp_eq_exp_mul_exp
    (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2))
    (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)) c

private theorem map_mk_pow_eq_bot {A : Type*} [Ring A] (I : Ideal A) [I.IsTwoSided] (n : ℕ) :
    (Ideal.map (Ideal.Quotient.mk (I ^ n)) I) ^ n = ⊥ := by
  have hmem (K : Ideal A) {x : A ⧸ I ^ n} (hx : x ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) K) :
      ∃ a ∈ K, Ideal.Quotient.mk (I ^ n) a = x := by
    refine Submodule.span_induction (fun _ ⟨a, ha, h⟩ => ⟨a, ha, h⟩) ⟨0, K.zero_mem, map_zero _⟩
      (fun _ _ _ _ ⟨a, ha, hfa⟩ ⟨b, hb, hfb⟩ =>
        ⟨a + b, K.add_mem ha hb, by rw [map_add, hfa, hfb]⟩)
      (fun r _ _ ⟨a, ha, hfa⟩ => ?_) hx
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact ⟨c * a, K.mul_mem_left c ha, by rw [smul_eq_mul, map_mul, hfa]⟩
  have hle (m : ℕ) :
      (Ideal.map (Ideal.Quotient.mk (I ^ n)) I) ^ m ≤
        Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ m) := by
    induction m with
    | zero =>
      rw [Submodule.pow_zero, Submodule.pow_zero, Ideal.one_eq_top, Ideal.one_eq_top,
        Ideal.map_top (Ideal.Quotient.mk (I ^ n))]
    | succ m ih =>
      rw [Submodule.pow_succ, Submodule.pow_succ]
      refine (Ideal.mul_mono_left ih).trans (Ideal.mul_le.mpr fun x hx y hy => ?_)
      obtain ⟨a, ha, rfl⟩ := hmem (I ^ m) hx
      obtain ⟨b, hb, rfl⟩ := hmem I hy
      rw [← map_mul]
      exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_mul ha hb)
  refine le_bot_iff.mp ((hle n).trans fun x hx => ?_)
  obtain ⟨a, ha, rfl⟩ := hmem (I ^ n) hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

private theorem mk_ι_mem_map_augmentation (n : ℕ) (x : F₂) :
    Ideal.Quotient.mk (J₂ ^ n) (_root_.UniversalEnvelopingAlgebra.ι ℚ x) ∈
      Ideal.map (Ideal.Quotient.mk (J₂ ^ n)) J₂ :=
  Ideal.mem_map_of_mem _
    (HopfIdeal.mem_toIdeal.mpr (UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ F₂ x))

/-- In class zero, `bchElement 0` is zero. -/
@[simp]
theorem bchElement_zero : bchElement 0 = 0 := by
  symm
  apply eq_bchElement_of_lowerCentralQuotientι_eq 0
  have h0 (x : F₂) :
      Ideal.Quotient.mk (J₂ ^ (0 + 1)) (_root_.UniversalEnvelopingAlgebra.ι ℚ x) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, Submodule.pow_one]
    exact HopfIdeal.mem_toIdeal.mpr (UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ F₂ x)
  simp only [map_zero, h0, IsNilpotent.exp_zero, mul_one, IsNilpotent.log_one]

/-- In class one (abelianization), `bchElement 1` is `X + Y`. -/
theorem bchElement_one :
    bchElement 1 =
      LieSubmodule.Quotient.mk
        (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2) + _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)) := by
  symm
  apply eq_bchElement_of_lowerCentralQuotientι_eq 1
  have hpow : (Ideal.map (Ideal.Quotient.mk (J₂ ^ 2)) J₂) ^ 3 = ⊥ :=
    le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega : 2 ≤ 3)).trans (map_mk_pow_eq_bot J₂ 2).le)
  rw [Ideal.log_exp_mul_exp_of_pow_three_eq_bot _ hpow
    (mk_ι_mem_map_augmentation 2 _) (mk_ι_mem_map_augmentation 2 _)]
  simp only [UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk, map_add, Ring.lie_def,
    _root_.UniversalEnvelopingAlgebra.ι_apply, UniversalEnvelopingAlgebra.quotient_ι_mul_ι,
    sub_self, smul_zero, add_zero]

/-- In class two, `bchElement 2` is `X + Y + ½ ⁅X, Y⁆`. -/
theorem bchElement_two :
    bchElement 2 =
      LieSubmodule.Quotient.mk
        (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2) + _root_.FreeLieAlgebra.of ℚ (1 : Fin 2) +
          (1 / 2 : ℚ) • ⁅_root_.FreeLieAlgebra.of ℚ (0 : Fin 2),
            _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)⁆) := by
  symm
  apply eq_bchElement_of_lowerCentralQuotientι_eq 2
  rw [Ideal.log_exp_mul_exp_of_pow_three_eq_bot _ (map_mk_pow_eq_bot J₂ 3)
    (mk_ι_mem_map_augmentation 3 _) (mk_ι_mem_map_augmentation 3 _)]
  simp only [UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk, ← Ideal.Quotient.mkₐ_eq_mk ℚ,
    map_add, map_smul, LieHom.map_lie, LieRing.of_associative_ring_bracket, map_sub, map_mul]

/-- In class three, `bchElement 3` is `X + Y + ½ ⁅X, Y⁆ + 1/12 (⁅X, ⁅X, Y⁆⁆ + ⁅Y, ⁅Y, X⁆⁆)`. -/
theorem bchElement_three :
    bchElement 3 =
      LieSubmodule.Quotient.mk
        (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2) + _root_.FreeLieAlgebra.of ℚ (1 : Fin 2) +
          (1 / 2 : ℚ) • ⁅_root_.FreeLieAlgebra.of ℚ (0 : Fin 2),
            _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)⁆ +
          (1 / 12 : ℚ) •
            (⁅_root_.FreeLieAlgebra.of ℚ (0 : Fin 2),
                ⁅_root_.FreeLieAlgebra.of ℚ (0 : Fin 2),
                  _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)⁆⁆ +
              ⁅_root_.FreeLieAlgebra.of ℚ (1 : Fin 2),
                ⁅_root_.FreeLieAlgebra.of ℚ (1 : Fin 2),
                  _root_.FreeLieAlgebra.of ℚ (0 : Fin 2)⁆⁆)) := by
  symm
  apply eq_bchElement_of_lowerCentralQuotientι_eq 3
  rw [Ideal.log_exp_mul_exp_of_pow_four_eq_bot _ (map_mk_pow_eq_bot J₂ 4)
    (mk_ι_mem_map_augmentation 4 _) (mk_ι_mem_map_augmentation 4 _)]
  simp only [UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk, ← Ideal.Quotient.mkₐ_eq_mk ℚ,
    map_add, map_smul, LieHom.map_lie, LieRing.of_associative_ring_bracket, map_sub, map_mul]

end Universal

end TauCeti.FreeLieAlgebra
