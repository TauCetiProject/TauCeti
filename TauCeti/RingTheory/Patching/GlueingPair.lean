/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Ideal
public import TauCeti.Algebra.Module.Torsion.Basic
public import TauCeti.RingTheory.Localization.Away.Quotient
public import TauCeti.RingTheory.Patching.ExactSquare
import Mathlib.Tactic.LinearCombination

/-!
# Glueing pairs

Let `R → R'` be a map of commutative rings and `f ∈ R`. Write `f'` for the image of `f` in `R'`,
`M[f^∞]` for the `f`-power torsion of a module `M`, `R_f` for a localization of `R` away from `f`
and `R'_f` for a localization of `R'` away from `f'`. The pair `(R → R', f)` is a *glueing pair*
when `R → R'` induces isomorphisms `R ⧸ fⁿ ≃ R' ⧸ f'ⁿ` for every `n` and a bijection
`R[f^∞] → R'[f^∞]`. Equivalently, the square

```
R   ⟶ R'
↓      ↓
R_f ⟶ R'_f
```

is exact in the sense of `TauCeti.ExactSquare`: the sequence `0 → R → R' × R_f → R'_f → 0` is
exact. This is the setting of the Beauville–Laszlo theorem, which identifies the *glueable*
`R`-modules (Stacks, Section 15.92) with glueing data over the square: a module over `R'`, a
module over `R_f` and an isomorphism of their base changes to `R'_f`. No flatness of `R → R'` is
required, but the theorem concerns glueable modules, not arbitrary `R`-modules. The main example
is the `f`-adic completion `R → R̂` of a ring in which `f` is a nonzerodivisor
(`IsRegular.glueingPair_adicCompletion`); no noetherian hypothesis is needed.

Given the isomorphisms modulo powers of `f`, the sequence is always exact on the right. It is
exact on the left exactly when `R[f^∞] → R'[f^∞]` is injective, since the kernel of `R → R_f` is
`R[f^∞]`, and exact in the middle exactly when `R[f^∞] → R'[f^∞]` is surjective. Conversely, an
exact square already induces the isomorphisms modulo powers of `f`.

## Main definitions

* `TauCeti.GlueingPair R' f`: the pair `(R → R', f)` is a glueing pair.

## Main results

* `TauCeti.glueingPair_iff`: `(R → R', f)` is a glueing pair if and only if the canonical maps
  `R ⧸ (fⁿ) → R' ⧸ (f'ⁿ)` and `R[f^∞] → R'[f^∞]` are bijective.
* `TauCeti.GlueingPair.quotientMap_bijective`: a glueing pair induces isomorphisms
  `R ⧸ (fⁿ) ≃ R' ⧸ (f'ⁿ)`.
* `TauCeti.injective_algebraMap_prod_iff_injOn_torsion'`,
  `TauCeti.surjective_sub_of_quotient_surjective`: the patching sequence is exact on the left
  exactly when `R[f^∞] → R'[f^∞]` is injective, and exact on the right as soon as `R → R'` is
  surjective modulo every power of `f`.
* `TauCeti.GlueingPair.exactSquare`: the square `R → R'`, `R_f → R'_f` of a glueing pair is
  exact.
* `TauCeti.glueingPair_iff_exactSquare`: the torsion criterion. The pair is a glueing pair if
  and only if the square is exact.
* `TauCeti.GlueingPair.exists_isPrime_comap_eq`: for a glueing pair, every prime of `R` comes
  from a prime of `R'` or of `R_f`. This specializes
  `TauCeti.exists_isPrime_comap_eq_of_bijective_quotientMap`.
* `TauCeti.glueingPair_self`: the identity `R → R` is a glueing pair for every `f`.

## References

* [The Stacks Project, Section 15.92](https://stacks.math.columbia.edu/tag/0BNI), glueing pairs:
  Lemma 15.92.3 for the primes, Lemma 15.92.6 (Tag 0BNR) for the torsion criterion and
  Remark 15.92.7 (Tag 0BNS) for the completion at a nonzerodivisor, which is
  `IsRegular.glueingPair_adicCompletion` in `TauCeti.RingTheory.AdicCompletion.Fracture`.
* A. Beauville, Y. Laszlo, *Un lemme de descente*, C. R. Acad. Sci. Paris Sér. I Math. 320
  (1995), 335–340.
-/

public section

namespace TauCeti

variable {R R' : Type*} [CommRing R] [CommRing R']

section Definition

variable [Algebra R R']

variable (R') in
/-- The pair `(R → R', f)` is a *glueing pair* when `R → R'` induces isomorphisms
`R ⧸ (fⁿ) ≃ R' ⧸ (f'ⁿ)` for every `n`, where `f'` is the image of `f`, and a bijection between
the `f`-power torsion of `R` and the `f'`-power torsion of `R'`. Equivalently, the sequence
`0 → R → R' × R_f → R'_f → 0` is exact (`TauCeti.glueingPair_iff_exactSquare`). -/
structure GlueingPair (f : R) : Prop where
  /-- Every element of `R'` is congruent modulo `f'ⁿ` to the image of an element of `R`. -/
  quotient_surjective : ∀ (n : ℕ) (y : R'), ∃ x : R,
    y - algebraMap R R' x ∈ Ideal.span {algebraMap R R' f ^ n}
  /-- An element of `R` whose image is divisible by `f'ⁿ` is divisible by `fⁿ`. -/
  quotient_injective : ∀ n : ℕ,
    (Ideal.span {algebraMap R R' f ^ n}).comap (algebraMap R R') = Ideal.span {f ^ n}
  /-- The map `R → R'` restricts to a bijection between the power torsion submodules. -/
  torsion_bijOn : Set.BijOn (algebraMap R R')
    (Submodule.torsion' R R (Submonoid.powers f))
    (Submodule.torsion' R' R' (Submonoid.powers (algebraMap R R' f)))

/-- The canonical map `R ⧸ (fⁿ) → R' ⧸ (f'ⁿ)` is bijective if and only if every element of `R'`
is congruent modulo `f'ⁿ` to the image of an element of `R` and an element of `R` whose image is
divisible by `f'ⁿ` is divisible by `fⁿ`. -/
theorem bijective_quotientMap_iff {f : R} {n : ℕ} :
    Function.Bijective (Ideal.quotientMap ((Ideal.span {f ^ n}).map (algebraMap R R'))
      (algebraMap R R') Ideal.le_comap_map) ↔
      (∀ y : R', ∃ x : R, y - algebraMap R R' x ∈ Ideal.span {algebraMap R R' f ^ n}) ∧
        (Ideal.span {algebraMap R R' f ^ n}).comap (algebraMap R R') = Ideal.span {f ^ n} := by
  have hJ : (Ideal.span {f ^ n}).map (algebraMap R R') = Ideal.span {algebraMap R R' f ^ n} := by
    simp [Ideal.map_span]
  rw [← hJ, Function.Bijective, and_comm]
  refine and_congr ⟨fun h y ↦ ?_, fun h y ↦ ?_⟩ ?_
  · obtain ⟨x, hx⟩ := h (Ideal.Quotient.mk _ y)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨x, Ideal.Quotient.eq.mp (hx.symm.trans Ideal.quotientMap_mk)⟩
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := h y
    exact ⟨Ideal.Quotient.mk _ x, (Ideal.Quotient.eq.mpr hx).symm⟩
  · rw [Ideal.quotientMap, Ideal.injective_lift_iff, ← RingHom.comap_ker, Ideal.mk_ker]

/-- `(R → R', f)` is a glueing pair if and only if the canonical maps `R ⧸ (fⁿ) → R' ⧸ (f'ⁿ)` are
bijective for every `n` and `R → R'` restricts to a bijection `R[f^∞] → R'[f^∞]`. -/
theorem glueingPair_iff {f : R} : GlueingPair R' f ↔
    (∀ n : ℕ, Function.Bijective
      (Ideal.quotientMap ((Ideal.span {f ^ n}).map (algebraMap R R'))
      (algebraMap R R') Ideal.le_comap_map)) ∧
      Set.BijOn (algebraMap R R') (Submodule.torsion' R R (Submonoid.powers f))
        (Submodule.torsion' R' R' (Submonoid.powers (algebraMap R R' f))) :=
  ⟨fun h ↦ ⟨fun _ ↦ bijective_quotientMap_iff.mpr ⟨h.quotient_surjective _, h.quotient_injective _⟩,
      h.torsion_bijOn⟩,
    fun h ↦ ⟨fun n ↦ (bijective_quotientMap_iff.mp (h.1 n)).1,
      fun n ↦ (bijective_quotientMap_iff.mp (h.1 n)).2, h.2⟩⟩

/-- A glueing pair induces isomorphisms `R ⧸ (fⁿ) ≃ R' ⧸ (f'ⁿ)` for every `n`. -/
theorem GlueingPair.quotientMap_bijective {f : R} (h : GlueingPair R' f) (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap ((Ideal.span {f ^ n}).map (algebraMap R R'))
      (algebraMap R R') Ideal.le_comap_map) :=
  (glueingPair_iff.mp h).1 n

end Definition

variable (R) in
/-- The identity map of a ring is a glueing pair for every element. -/
theorem glueingPair_self (f : R) : GlueingPair R f where
  quotient_surjective _ y := ⟨y, by simp⟩
  quotient_injective _ := by simp
  torsion_bijOn := by simpa using Set.bijOn_id _

section ExactSquare

variable {R₂ L : Type*} [CommRing R₂] [CommRing L] [Algebra R R'] [Algebra R R₂] [Algebra R L]
  [Algebra R' L] [Algebra R₂ L] [IsScalarTower R R' L] [IsScalarTower R R₂ L] {f : R}

omit [Algebra R L] [Algebra R' L] [Algebra R₂ L] [IsScalarTower R R' L] [IsScalarTower R R₂ L] in
variable (R' R₂) in
/-- The diagonal `R → R' × R_f` is injective exactly when `R[f^∞] → R'[f^∞]` is injective
(Stacks, Lemma 15.92.6). -/
theorem injective_algebraMap_prod_iff_injOn_torsion' [IsLocalization.Away f R₂] :
    Function.Injective (fun r : R ↦ (algebraMap R R' r, algebraMap R R₂ r)) ↔
      Set.InjOn (algebraMap R R') (Submodule.torsion' R R (Submonoid.powers f)) := by
  have hz := IsLocalization.map_eq_zero_iff (Submonoid.powers f) R₂
  refine ⟨fun hi x hx y hy hxy ↦ hi ?_, fun hi x y hxy ↦ ?_⟩
  · simp [hxy, (hz x).mpr hx, (hz y).mpr hy]
  · simp only [Prod.mk.injEq] at hxy
    rw [← sub_eq_zero]
    refine hi ((hz _).mp ?_) (zero_mem _) (by simp [hxy.1])
    simp [hxy.2]

/-- If every element of `R'` is congruent modulo every power of `f'` to the image of an element
of `R`, then the difference map `R' × R_f → R'_f` is surjective: the patching sequence is exact on
the right (Stacks, Lemma 15.92.6). -/
theorem surjective_sub_of_quotient_surjective [IsLocalization.Away f R₂]
    [IsLocalization.Away (algebraMap R R' f) L]
    (hs : ∀ (n : ℕ) (y : R'), ∃ x : R, y - algebraMap R R' x ∈ Ideal.span {algebraMap R R' f ^ n}) :
    Function.Surjective fun x : R' × R₂ ↦ algebraMap R' L x.1 - algebraMap R₂ L x.2 := by
  intro z
  obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj (algebraMap R R' f) z
  obtain ⟨a, ha⟩ := hs n r
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ha
  -- `z = r / f'ⁿ = b + a / fⁿ`, and `a / fⁿ` comes from `R_f`.
  let d : Submonoid.powers f := ⟨f ^ n, n, rfl⟩
  let s : R₂ := IsLocalization.mk' R₂ a d
  have hs : algebraMap R₂ L s * algebraMap R' L (algebraMap R R' f) ^ n =
      algebraMap R' L (algebraMap R R' a) := by
    simpa [d, ← IsScalarTower.algebraMap_apply] using
      congr(algebraMap R₂ L $(IsLocalization.mk'_spec R₂ a d))
  have hb : algebraMap R' L b * algebraMap R' L (algebraMap R R' f) ^ n =
      algebraMap R' L r - algebraMap R' L (algebraMap R R' a) := by
    simpa using congr(algebraMap R' L $hb)
  refine ⟨(b, -s), ((IsLocalization.Away.algebraMap_isUnit (S := L)
    (algebraMap R R' f)).pow n).mul_left_inj.mp ?_⟩
  simp only [map_neg, sub_neg_eq_add]
  linear_combination hb + hs - hr

/-- If every element of `R` whose image is divisible by `f'ⁿ` is divisible by `fⁿ` and
`R[f^∞] → R'[f^∞]` is surjective, then a pair `(r', s) ∈ R' × R_f` with the same image in `R'_f`
comes from `R`. Writing `s = a / fⁿ`, the element `a` is corrected by a torsion element to become
divisible by `fⁿ`, and the quotient is then corrected by a second torsion element. -/
private theorem exists_algebraMap_eq_of_surjOn_torsion' [IsLocalization.Away f R₂]
    [IsLocalization.Away (algebraMap R R' f) L]
    (hi : ∀ n : ℕ,
      (Ideal.span {algebraMap R R' f ^ n}).comap (algebraMap R R') ≤ Ideal.span {f ^ n})
    (hsurj : Set.SurjOn (algebraMap R R') (Submodule.torsion' R R (Submonoid.powers f))
      (Submodule.torsion' R' R' (Submonoid.powers (algebraMap R R' f))))
    {r' : R'} {s : R₂} (hrs : algebraMap R' L r' = algebraMap R₂ L s) :
    ∃ r : R, algebraMap R R' r = r' ∧ algebraMap R R₂ r = s := by
  -- Write `s = a / fⁿ`; then `f'ⁿ r' - a` is torsion in `R'`.
  obtain ⟨n, a, hs⟩ := IsLocalization.Away.surj f s
  have hsL : algebraMap R₂ L s * algebraMap R L f ^ n = algebraMap R L a := by
    simpa [← IsScalarTower.algebraMap_apply] using congr(algebraMap R₂ L $hs)
  have ht : algebraMap R R' f ^ n * r' - algebraMap R R' a ∈
      Submodule.torsion' R' R' (Submonoid.powers (algebraMap R R' f)) := by
    refine (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R R' f)) L _).mp ?_
    simp only [map_sub, map_mul, map_pow, hrs, ← IsScalarTower.algebraMap_apply]
    linear_combination hsL
  -- Correct `a` by a torsion element `t` to make it divisible by `fⁿ`: `a + t = fⁿ c`.
  obtain ⟨t, ht, htr⟩ := hsurj ht
  have hat : a + t ∈ (Ideal.span {algebraMap R R' f ^ n}).comap (algebraMap R R') :=
    Ideal.mem_comap.mpr <| Ideal.mem_span_singleton'.mpr ⟨r', by rw [map_add, htr]; ring⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hi n hat)
  -- Then `r' - c` is torsion in `R'`; lift it to a torsion element `u` of `R`.
  have hcR' : algebraMap R R' c * algebraMap R R' f ^ n = algebraMap R R' f ^ n * r' := by
    simpa [htr] using congr(algebraMap R R' $hc)
  have hv : r' - algebraMap R R' c ∈
      Submodule.torsion' R' R' (Submonoid.powers (algebraMap R R' f)) :=
    ⟨⟨_, pow_mem (Submonoid.mem_powers _) n⟩, by
      rw [Submonoid.smul_def, smul_eq_mul]
      linear_combination -hcR'⟩
  obtain ⟨u, hu, hur⟩ := hsurj hv
  -- The numerators of `c + u` and `s` differ by the torsion element `t + fⁿ u`.
  have h0 : algebraMap R R₂ (t + f ^ n * u) = 0 :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers f) R₂ _).mpr
      (add_mem ht (Submodule.smul_mem _ (f ^ n) hu))
  have hcR₂ := congr(algebraMap R R₂ $hc)
  refine ⟨c + u, by rw [map_add, hur, add_sub_cancel], ?_⟩
  refine ((IsLocalization.Away.algebraMap_isUnit f).pow n).mul_left_inj.mp ?_
  simp only [map_add, map_mul, map_pow] at h0 hcR₂ ⊢
  linear_combination hcR₂ + h0 - hs

omit [Algebra R L] [IsScalarTower R R' L] [IsScalarTower R R₂ L] in
/-- If the patching sequence `R → R' × R_f → R'_f` is exact in the middle, then
`R[f^∞] → R'[f^∞]` is surjective (Stacks, Lemma 15.92.6): a torsion element `t` of `R'` gives the
compatible pair `(t, 0)`. -/
private theorem surjOn_torsion'_of_exact [IsLocalization.Away f R₂]
    [IsLocalization.Away (algebraMap R R' f) L]
    (he : Function.Exact (fun r : R ↦ (algebraMap R R' r, algebraMap R R₂ r))
      (fun x : R' × R₂ ↦ algebraMap R' L x.1 - algebraMap R₂ L x.2)) :
    Set.SurjOn (algebraMap R R') (Submodule.torsion' R R (Submonoid.powers f))
      (Submodule.torsion' R' R' (Submonoid.powers (algebraMap R R' f))) := by
  intro t ht
  obtain ⟨r, hr⟩ := (he (t, 0)).mp
    (by simp [(IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R R' f)) L t).mpr ht])
  simp only [Prod.mk.injEq] at hr
  exact ⟨r, (IsLocalization.map_eq_zero_iff (Submonoid.powers f) R₂ r).mp hr.2, hr.1⟩

/-- If every element of `R` whose image is divisible by `f'ⁿ` is divisible by `fⁿ` and
`R[f^∞] → R'[f^∞]` is surjective, then the patching sequence `R → R' × R_f → R'_f` is exact in
the middle (Stacks, Lemma 15.92.6). -/
private theorem exact_of_surjOn_torsion' [IsLocalization.Away f R₂]
    [IsLocalization.Away (algebraMap R R' f) L]
    (hi : ∀ n : ℕ,
      (Ideal.span {algebraMap R R' f ^ n}).comap (algebraMap R R') ≤ Ideal.span {f ^ n})
    (hsurj : Set.SurjOn (algebraMap R R') (Submodule.torsion' R R (Submonoid.powers f))
      (Submodule.torsion' R' R' (Submonoid.powers (algebraMap R R' f)))) :
    Function.Exact (fun r : R ↦ (algebraMap R R' r, algebraMap R R₂ r))
      (fun x : R' × R₂ ↦ algebraMap R' L x.1 - algebraMap R₂ L x.2) := by
  refine fun x ↦ ⟨fun hrs ↦ ?_, ?_⟩
  · obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_surjOn_torsion' hi hsurj (sub_eq_zero.mp hrs)
    exact ⟨r, Prod.ext hr.1 hr.2⟩
  · rintro ⟨r, rfl⟩
    simp [← IsScalarTower.algebraMap_apply]

variable (R₂ L) in
/-- The square `R → R'`, `R_f → R'_f` of a glueing pair is exact: the sequence
`0 → R → R' × R_f → R'_f → 0` is exact (Stacks, Lemma 15.92.6). -/
theorem GlueingPair.exactSquare (h : GlueingPair R' f) [IsLocalization.Away f R₂]
    [IsLocalization.Away (algebraMap R R' f) L] : ExactSquare R R' R₂ L where
  injective := (injective_algebraMap_prod_iff_injOn_torsion' R' R₂).mpr h.torsion_bijOn.injOn
  exact := exact_of_surjOn_torsion' (fun n ↦ (h.quotient_injective n).le) h.torsion_bijOn.surjOn
  surjective := surjective_sub_of_quotient_surjective h.quotient_surjective

/-- In an exact square `R → R'`, `R_f → R'_f`, every element `y` of `R'` is congruent modulo
`f'ⁿ` to the image of an element of `R`: write `y / f'ⁿ = a - s` in `R'_f`, so that the pair
`(y - f'ⁿ a, -fⁿ s)` is compatible. -/
private theorem quotient_surjective_of_exactSquare
    [IsLocalization.Away (algebraMap R R' f) L] (h : ExactSquare R R' R₂ L) (n : ℕ) (y : R') :
    ∃ x : R, y - algebraMap R R' x ∈ Ideal.span {algebraMap R R' f ^ n} := by
  let d : Submonoid.powers (algebraMap R R' f) := ⟨algebraMap R R' f ^ n, n, rfl⟩
  obtain ⟨⟨a, s⟩, has⟩ := h.surjective (IsLocalization.mk' L y d)
  have hspec := IsLocalization.mk'_spec L y d
  rw [← has] at hspec
  obtain ⟨x, hx, -⟩ := (h.exists_algebraMap_eq_iff (y - algebraMap R R' f ^ n * a)
    (-(algebraMap R R₂ f ^ n * s))).mpr (by
      simp only [d, map_sub, map_mul, map_pow, map_neg, ← IsScalarTower.algebraMap_apply]
        at hspec ⊢
      linear_combination -hspec)
  exact ⟨x, Ideal.mem_span_singleton'.mpr ⟨a, by rw [hx]; ring⟩⟩

/-- In an exact square `R → R'`, `R_f → R'_f`, an element `x` of `R` whose image is `f'ⁿ y` is
divisible by `fⁿ`: the pair `(y, x / fⁿ)` is compatible, so it comes from some `z` with
`x = fⁿ z`. -/
private theorem comap_span_pow_le_of_exactSquare [IsLocalization.Away f R₂]
    [IsLocalization.Away (algebraMap R R' f) L] (h : ExactSquare R R' R₂ L) (n : ℕ) :
    (Ideal.span {algebraMap R R' f ^ n}).comap (algebraMap R R') ≤ Ideal.span {f ^ n} := by
  intro x hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hx)
  let d : Submonoid.powers f := ⟨f ^ n, n, rfl⟩
  have hspec : IsLocalization.mk' R₂ x d * algebraMap R R₂ f ^ n = algebraMap R R₂ x := by
    simpa [d] using IsLocalization.mk'_spec R₂ x d
  have hu : IsUnit (algebraMap R L f) := by
    rw [IsScalarTower.algebraMap_apply R R' L]
    exact IsLocalization.Away.algebraMap_isUnit _
  obtain ⟨z, hz, hz'⟩ := (h.exists_algebraMap_eq_iff y (IsLocalization.mk' R₂ x d)).mpr <|
    (hu.pow n).mul_left_inj.mp (by
      have hspecL := congr(algebraMap R₂ L $hspec)
      have hyL := congr(algebraMap R' L $hy)
      simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at hspecL hyL
      rw [hyL, hspecL])
  refine Ideal.mem_span_singleton'.mpr ⟨z, h.injective (Prod.ext ?_ ?_)⟩
  · simp only [map_mul, map_pow, hz, hy]
  · simp only [map_mul, map_pow, hz', hspec]

/-- The torsion criterion for glueing pairs (Stacks, Lemma 15.92.6). The pair `(R → R', f)` is a
glueing pair if and only if the square `R → R'`, `R_f → R'_f` is exact. Exactness of the square
already forces the isomorphisms `R ⧸ (fⁿ) ≃ R' ⧸ (f'ⁿ)`, so no hypothesis on the quotients is
needed. -/
theorem glueingPair_iff_exactSquare [IsLocalization.Away f R₂]
    [IsLocalization.Away (algebraMap R R' f) L] :
    GlueingPair R' f ↔ ExactSquare R R' R₂ L :=
  ⟨fun h ↦ h.exactSquare R₂ L, fun h ↦
    { quotient_surjective := quotient_surjective_of_exactSquare h
      quotient_injective := fun n ↦
        le_antisymm (comap_span_pow_le_of_exactSquare h n)
          ((Ideal.le_comap_map (f := algebraMap R R') (I := Ideal.span {f ^ n})).trans_eq
            (by simp [Ideal.map_span]))
      torsion_bijOn := ⟨(algebraMap R R').mapsTo_torsion'_powers f,
        (injective_algebraMap_prod_iff_injOn_torsion' R' R₂).mp h.injective,
        surjOn_torsion'_of_exact h.exact⟩ }⟩

omit [Algebra R L] [Algebra R' L] [Algebra R₂ L] [IsScalarTower R R' L] [IsScalarTower R R₂ L] in
/-- Every prime ideal of `R` is the contraction of a prime ideal of `R'` or of `R_f` for a glueing
pair `(R → R', f)` (Stacks, Lemma 15.92.3). -/
theorem GlueingPair.exists_isPrime_comap_eq (h : GlueingPair R' f) [IsLocalization.Away f R₂]
    (p : Ideal R) [p.IsPrime] :
    (∃ P : Ideal R', P.IsPrime ∧ P.comap (algebraMap R R') = p) ∨
      ∃ P : Ideal R₂, P.IsPrime ∧ P.comap (algebraMap R R₂) = p := by
  have hi := h.quotient_injective 1
  simp only [pow_one] at hi
  exact exists_isPrime_comap_eq_of_bijective_quotientMap (H := hi.ge)
    (by convert h.quotientMap_bijective 1 <;> simp [Ideal.map_span]) p

end ExactSquare

end TauCeti
