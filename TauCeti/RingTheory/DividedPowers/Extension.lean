/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.DividedPowers.SubDPIdeal
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Localization
import TauCeti.RingTheory.DividedPowers.Generators
import TauCeti.RingTheory.PowerSeries.CoeffProd

/-!
# Extension of divided powers along principal ideals, flat maps, and localizations

Given a divided power structure `hI` on an ideal `I` of a commutative ring `A` and a ring
homomorphism `f : A →+* B`, an extension of `hI` to `I.map f` is a divided power structure `hB` on
`I.map f` making `f` a divided power morphism. By `DividedPowers.ext_of_isDPMorphism_map`, such an
extension is always unique if it exists, without any flatness or injectivity assumption on `f`.

This file constructs the extension in the two main cases of Stacks Project, Lemma 23.4.2 (tag
07H1), together with the localization specialization needed for quasi-coherent PD ideals on schemes:

1. **Principal ideals** (`DividedPowers.mapOfSpanSingleton`): when `I = Ideal.span {x}`, `hI`
   extends uniquely to `I.map f` along *any* homomorphism `f : A →+* B` of commutative semirings,
   with `(hI.mapOfSpanSingleton f hIx).dpow n (b * f x) = b ^ n * f (hI.dpow n x)`.
2. **Flat algebras** (`DividedPowers.mapOfFlat`): when `B` is a flat `A`-algebra, `hI` extends
   uniquely to `I.map (algebraMap A B)`. The candidate value on
   `∑ i ∈ s, b i * algebraMap A B (x i)` is `DividedPowers.extensionCoeff`, identified via
   `DividedPowers.dpow_sum'` with the `n`-th coefficient of
   `∏ i ∈ s, PowerSeries.rescale (b i) (PowerSeries.map f (hI.exp (x i)))`.
   Bimultiplicativity of `PowerSeries.rescale` and `DividedPowers.exp` yields invariance under
   finite scalar substitutions (`DividedPowers.extensionCoeff_subst`), and the equational criterion
   of flatness (`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`) yields presentation
   independence (`DividedPowers.extensionCoeff_eq_of_sum_eq`). Upgrading the resulting
   `AdditivePowers` via `DividedPowers.AdditivePowers.toDividedPowers` produces `mapOfFlat`.
3. **Localizations** (`DividedPowers.mapOfIsLocalization`): since every localization is flat
   (`IsLocalization.flat`), `hI` extends uniquely to `I.map (algebraMap A B)` with
   `dpow n (IsLocalization.mk' B x s) = IsLocalization.mk' B (hI.dpow n x) (s ^ n)`.

## Main declarations

* `DividedPowers.ext_of_isDPMorphism_map`: uniqueness of an extension to `I.map f`.
* `DividedPowers.isDPMorphism_comp_iff_of_map`: universal property of any extension to `I.map f`.
* `DividedPowers.mapOfSpanSingleton`: extension of divided powers on a principal ideal along any
  semiring homomorphism.
* `DividedPowers.extensionCoeff`: the multiset-indexed scalar-extension coefficient formula.
* `DividedPowers.extensionCoeff_subst`: invariance of `extensionCoeff` under finite scalar
  substitutions.
* `DividedPowers.extensionCoeff_eq_of_sum_eq`: presentation independence of `extensionCoeff` over a
  flat algebra.
* `DividedPowers.mapOfFlat`: extension of divided powers along a flat algebra map, with
  transitivity (`mapOfFlat_comp_dpow`) and comparison with `ofRingEquiv` and `mapOfSpanSingleton`.
* `DividedPowers.mapOfIsLocalization`: extension of divided powers along a localization, with the
  fraction formula `mapOfIsLocalization_dpow_mk'`.

## References

* [Stacks Project, Divided Power Algebra, Lemma 23.4.2 (Tag 07H1)](https://stacks.math.columbia.edu/tag/07H1)
-/

public section

open Finset

namespace DividedPowers

section Uniqueness

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C]
  {I : Ideal A} {K : Ideal C}

/-- **Uniqueness of extension** (Stacks 23.4.2, tag 07H1): at most one divided power structure on
`I.map f` makes `f : A →+* B` a divided power morphism out of `(I, hI)`. -/
theorem ext_of_isDPMorphism_map (hI : DividedPowers I) (f : A →+* B)
    {hB hB' : DividedPowers (I.map f)}
    (h1 : IsDPMorphism hI hB f) (h2 : IsDPMorphism hI hB' f) :
    hB = hB' := by
  ext n b hb
  exact ((mem_dpEqualizer_iff hB hB').mp
    (le_equalizer_of_isDPMorphism hI f le_rfl hB hB' h1 h2 hb)).2 n

/-- Universal property of an extension of divided powers to `I.map f`: a ring homomorphism
`g : B →+* C` is a divided power morphism out of `(I.map f, hB)` if and only if `g.comp f` is a
divided power morphism out of `(I, hI)`. -/
theorem isDPMorphism_comp_iff_of_map (hI : DividedPowers I) {f : A →+* B}
    {hB : DividedPowers (I.map f)} (hf : IsDPMorphism hI hB f)
    (hK : DividedPowers K) (g : B →+* C) :
    IsDPMorphism hB hK g ↔ IsDPMorphism hI hK (g.comp f) :=
  ⟨fun hg ↦ hg.comp hK hf, fun hgf ↦ IsDPMorphism.of_comp hI hB hK f g rfl hf hgf⟩

end Uniqueness

section Principal

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A}

/-- Shared binomial expansion step for `(b₁ + b₂) ^ n * f (hI.dpow n x)`. -/
private theorem add_pow_mul_map_dpow (hI : DividedPowers I) (f : A →+* B)
    (b₁ b₂ : B) {x : A} (hx : x ∈ I) (n : ℕ) :
    (b₁ + b₂) ^ n * f (hI.dpow n x) =
      ∑ k ∈ antidiagonal n, (b₁ ^ k.1 * f (hI.dpow k.1 x)) * (b₂ ^ k.2 * f (hI.dpow k.2 x)) := by
  rw [(Commute.all b₁ b₂).add_pow', sum_mul]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [← mem_antidiagonal.mp hk, nsmul_eq_mul]
  have hmul : f (hI.dpow k.1 x) * f (hI.dpow k.2 x) =
      ((k.1 + k.2).choose k.1 : B) * f (hI.dpow (k.1 + k.2) x) := by
    rw [← map_mul, hI.mul_dpow hx, map_mul, map_natCast]
  calc ((k.1 + k.2).choose k.1 : B) * (b₁ ^ k.1 * b₂ ^ k.2) * f (hI.dpow (k.1 + k.2) x)
      = b₁ ^ k.1 * b₂ ^ k.2 * (((k.1 + k.2).choose k.1 : B) * f (hI.dpow (k.1 + k.2) x)) := by
        ring
    _ = b₁ ^ k.1 * b₂ ^ k.2 * (f (hI.dpow k.1 x) * f (hI.dpow k.2 x)) := by rw [← hmul]
    _ = b₁ ^ k.1 * f (hI.dpow k.1 x) * (b₂ ^ k.2 * f (hI.dpow k.2 x)) := by ring

/-- **Well-definedness of the principal extension formula** (Stacks 23.4.2, tag 07H1): if
`I = Ideal.span {x}`, then `b * f x = c * f x` implies
`b ^ n * f (hI.dpow n x) = c ^ n * f (hI.dpow n x)` for all `n : ℕ`. -/
theorem pow_mul_map_dpow_eq_of_mul_eq (hI : DividedPowers I) (f : A →+* B)
    {x : A} (hIx : I = Ideal.span {x}) {b c : B} (hbc : b * f x = c * f x) (n : ℕ) :
    b ^ n * f (hI.dpow n x) = c ^ n * f (hI.dpow n x) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hx : x ∈ I := hIx ▸ Ideal.subset_span rfl
    have hmem : hI.dpow n x ∈ Ideal.span {x} := hIx ▸ hI.dpow_mem hn hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hmem
    have hstep : ∀ k : ℕ, b ^ k * (f x * f a) = c ^ k * (f x * f a) := fun k ↦ by
      induction k with
      | zero => simp
      | succ k ih =>
        calc b ^ (k + 1) * (f x * f a) = b ^ k * ((b * f x) * f a) := by ring
          _ = b ^ k * ((c * f x) * f a) := by rw [hbc]
          _ = c * (b ^ k * (f x * f a)) := by ring
          _ = c * (c ^ k * (f x * f a)) := by rw [ih]
          _ = c ^ (k + 1) * (f x * f a) := by ring
    rw [ha, map_mul]
    exact hstep n

private theorem exists_mul_map_of_mem_span_singleton (f : A →+* B) {x : A}
    (hIx : I = Ideal.span {x}) {z : B} (hz : z ∈ I.map f) :
    ∃ b : B, z = b * f x := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp
    (by rwa [hIx, Ideal.map_span, Set.image_singleton] at hz)
  exact ⟨b, mul_comm _ _⟩

private noncomputable def principalDpow (hI : DividedPowers I) (f : A →+* B)
    {x : A} (hIx : I = Ideal.span {x}) (n : ℕ) (z : B) : B :=
  open scoped Classical in
  if hz : z ∈ I.map f then
    (exists_mul_map_of_mem_span_singleton f hIx hz).choose ^ n * f (hI.dpow n x)
  else 0

private theorem principalDpow_mul (hI : DividedPowers I) (f : A →+* B)
    {x : A} (hIx : I = Ideal.span {x}) (b : B) (n : ℕ) :
    principalDpow hI f hIx n (b * f x) = b ^ n * f (hI.dpow n x) := by
  classical
  have hx : x ∈ I := hIx ▸ Ideal.subset_span rfl
  have hz : b * f x ∈ I.map f := (I.map f).mul_mem_left b (Ideal.mem_map_of_mem f hx)
  simp only [principalDpow, dite_eq_left hz]
  have hspec := (exists_mul_map_of_mem_span_singleton f hIx hz).choose_spec
  exact pow_mul_map_dpow_eq_of_mul_eq hI f hIx hspec.symm n

/-- **Extension of divided powers on a principal ideal** (Stacks 23.4.2, tag 07H1, condition (2)):
if `I = Ideal.span {x}`, then `hI` extends uniquely along any semiring homomorphism `f : A →+* B`
to a divided power structure on `I.map f`, sending `b * f x` to `b ^ n * f (hI.dpow n x)`. -/
noncomputable def mapOfSpanSingleton (hI : DividedPowers I) (f : A →+* B)
    {x : A} (hIx : I = Ideal.span {x}) : DividedPowers (I.map f) where
  dpow := principalDpow hI f hIx
  dpow_null {n z} hz := by
    classical
    simp [principalDpow, hz]
  dpow_zero {z} hz := by
    have hx : x ∈ I := hIx ▸ Ideal.subset_span rfl
    obtain ⟨b, rfl⟩ := exists_mul_map_of_mem_span_singleton f hIx hz
    rw [principalDpow_mul, pow_zero, one_mul, hI.dpow_zero hx, map_one]
  dpow_one {z} hz := by
    have hx : x ∈ I := hIx ▸ Ideal.subset_span rfl
    obtain ⟨b, rfl⟩ := exists_mul_map_of_mem_span_singleton f hIx hz
    rw [principalDpow_mul, pow_one, hI.dpow_one hx]
  dpow_mem {n z} hn hz := by
    have hx : x ∈ I := hIx ▸ Ideal.subset_span rfl
    obtain ⟨b, rfl⟩ := exists_mul_map_of_mem_span_singleton f hIx hz
    rw [principalDpow_mul]
    exact (I.map f).mul_mem_left _ (Ideal.mem_map_of_mem f (hI.dpow_mem hn hx))
  dpow_add {n z₁ z₂} hz₁ hz₂ := by
    have hx : x ∈ I := hIx ▸ Ideal.subset_span rfl
    obtain ⟨b₁, rfl⟩ := exists_mul_map_of_mem_span_singleton f hIx hz₁
    obtain ⟨b₂, rfl⟩ := exists_mul_map_of_mem_span_singleton f hIx hz₂
    rw [← add_mul, principalDpow_mul, add_pow_mul_map_dpow hI f b₁ b₂ hx n]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [principalDpow_mul, principalDpow_mul]
  dpow_mul {n a z} hz := by
    obtain ⟨b, rfl⟩ := exists_mul_map_of_mem_span_singleton f hIx hz
    rw [← mul_assoc, principalDpow_mul, principalDpow_mul, mul_pow, mul_assoc]
  mul_dpow {m n z} hz := by
    have hx : x ∈ I := hIx ▸ Ideal.subset_span rfl
    obtain ⟨b, rfl⟩ := exists_mul_map_of_mem_span_singleton f hIx hz
    rw [principalDpow_mul, principalDpow_mul, principalDpow_mul,
      mul_mul_mul_comm, ← pow_add, ← map_mul, hI.mul_dpow hx, map_mul, map_natCast]
    ring
  dpow_comp {m n z} hn hz := by
    have hx : x ∈ I := hIx ▸ Ideal.subset_span rfl
    obtain ⟨b, rfl⟩ := exists_mul_map_of_mem_span_singleton f hIx hz
    have hmem : hI.dpow n x ∈ Ideal.span {x} := hIx ▸ hI.dpow_mem hn hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hmem
    have hinner : principalDpow hI f hIx n (b * f x) = (b ^ n * f a) * f x := by
      rw [principalDpow_mul, ha, map_mul]
      ring
    calc
      principalDpow hI f hIx m (principalDpow hI f hIx n (b * f x))
        = principalDpow hI f hIx m ((b ^ n * f a) * f x) := by rw [hinner]
      _ = (b ^ n * f a) ^ m * f (hI.dpow m x) :=
          principalDpow_mul hI f hIx (b ^ n * f a) m
      _ = b ^ (m * n) * f (a ^ m * hI.dpow m x) := by
          simp only [map_mul, map_pow]
          ring
      _ = b ^ (m * n) * f (hI.dpow m (hI.dpow n x)) := by
          rw [← hI.dpow_mul hx, mul_comm a x, ← ha]
      _ = (Nat.uniformBell m n : B) * (b ^ (m * n) * f (hI.dpow (m * n) x)) := by
          rw [hI.dpow_comp hn hx]
          simp only [map_mul, map_natCast]
          ring
      _ = (Nat.uniformBell m n : B) * principalDpow hI f hIx (m * n) (b * f x) := by
          rw [principalDpow_mul]

/-- The formula for `DividedPowers.mapOfSpanSingleton` on a multiple `b * f x` of the generator. -/
@[simp]
theorem mapOfSpanSingleton_dpow_mul (hI : DividedPowers I) (f : A →+* B)
    {x : A} (hIx : I = Ideal.span {x}) (b : B) (n : ℕ) :
    (hI.mapOfSpanSingleton f hIx).dpow n (b * f x) = b ^ n * f (hI.dpow n x) := by
  rw [mapOfSpanSingleton]
  exact principalDpow_mul hI f hIx b n

/-- `f` is a divided power morphism from `(I, hI)` to `(I.map f, hI.mapOfSpanSingleton f hIx)`. -/
theorem isDPMorphism_mapOfSpanSingleton (hI : DividedPowers I) (f : A →+* B)
    {x : A} (hIx : I = Ideal.span {x}) :
    IsDPMorphism hI (hI.mapOfSpanSingleton f hIx) f where
  ideal_comp := le_rfl
  dpow_comp {n} a ha := by
    have hx : x ∈ I := hIx ▸ Ideal.subset_span rfl
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp (hIx ▸ ha)
    rw [mul_comm x r, map_mul, mapOfSpanSingleton_dpow_mul, hI.dpow_mul hx, map_mul, map_pow]

/-- On `f a` with `a ∈ I`, `mapOfSpanSingleton` agrees with `hI`. -/
theorem mapOfSpanSingleton_dpow_map (hI : DividedPowers I) (f : A →+* B)
    {x : A} (hIx : I = Ideal.span {x}) (n : ℕ) {a : A} (ha : a ∈ I) :
    (hI.mapOfSpanSingleton f hIx).dpow n (f a) = f (hI.dpow n a) :=
  (isDPMorphism_mapOfSpanSingleton hI f hIx).dpow_comp a ha

/-- `DividedPowers.mapOfSpanSingleton` is independent of the choice of generator of `I`. -/
theorem mapOfSpanSingleton_eq_of_span_eq (hI : DividedPowers I) (f : A →+* B)
    {x y : A} (hIx : I = Ideal.span {x}) (hIy : I = Ideal.span {y}) :
    hI.mapOfSpanSingleton f hIx = hI.mapOfSpanSingleton f hIy :=
  ext_of_isDPMorphism_map hI f (isDPMorphism_mapOfSpanSingleton hI f hIx)
    (isDPMorphism_mapOfSpanSingleton hI f hIy)

/-- A divided power structure on `I.map f` equals `hI.mapOfSpanSingleton f hIx` if and only if
`f` is a divided power morphism into it. -/
theorem eq_mapOfSpanSingleton_iff (hI : DividedPowers I) (f : A →+* B)
    {x : A} (hIx : I = Ideal.span {x}) (hB : DividedPowers (I.map f)) :
    hB = hI.mapOfSpanSingleton f hIx ↔ IsDPMorphism hI hB f :=
  ⟨fun h ↦ h ▸ isDPMorphism_mapOfSpanSingleton hI f hIx,
    fun hf ↦ ext_of_isDPMorphism_map hI f hf (isDPMorphism_mapOfSpanSingleton hI f hIx)⟩

/-- Universal property of `DividedPowers.mapOfSpanSingleton` for outgoing divided power
morphisms. -/
theorem isDPMorphism_mapOfSpanSingleton_iff {C : Type*} [CommSemiring C] {K : Ideal C}
    (hI : DividedPowers I) (f : A →+* B) {x : A} (hIx : I = Ideal.span {x})
    (hK : DividedPowers K) (g : B →+* C) :
    IsDPMorphism (hI.mapOfSpanSingleton f hIx) hK g ↔ IsDPMorphism hI hK (g.comp f) :=
  isDPMorphism_comp_iff_of_map hI (isDPMorphism_mapOfSpanSingleton hI f hIx) hK g

end Principal

section ExtensionCoeff

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A}

/-- The multiset-indexed scalar-extension coefficient formula
`∑_{k ∈ s.sym n} ∏_{i ∈ s} b i ^ (count i k) * f (hI.dpow (count i k) (x i))`. -/
def extensionCoeff {ι : Type*} [DecidableEq ι] (hI : DividedPowers I) (f : A →+* B)
    (n : ℕ) (s : Finset ι) (b : ι → B) (x : ι → A) : B :=
  ∑ k ∈ s.sym n, ∏ i ∈ s, b i ^ Multiset.count i k * f (hI.dpow (Multiset.count i k) (x i))

/-- The defining equation of `DividedPowers.extensionCoeff`. -/
theorem extensionCoeff_def {ι : Type*} [DecidableEq ι] (hI : DividedPowers I) (f : A →+* B)
    (n : ℕ) (s : Finset ι) (b : ι → B) (x : ι → A) :
    extensionCoeff hI f n s b x =
      ∑ k ∈ s.sym n, ∏ i ∈ s,
        b i ^ Multiset.count i k * f (hI.dpow (Multiset.count i k) (x i)) :=
  (rfl)

/-- `extensionCoeff` depends only on the values of `b` and `x` on `s`. -/
theorem extensionCoeff_congr {ι : Type*} [DecidableEq ι] (hI : DividedPowers I) (f : A →+* B)
    (n : ℕ) {s : Finset ι} {b b' : ι → B} {x x' : ι → A}
    (hb : ∀ i ∈ s, b i = b' i) (hx : ∀ i ∈ s, x i = x' i) :
    extensionCoeff hI f n s b x = extensionCoeff hI f n s b' x' := by
  rw [extensionCoeff_def, extensionCoeff_def]
  refine sum_congr rfl fun k _ ↦ prod_congr rfl fun i hi ↦ ?_
  rw [hb i hi, hx i hi]

/-- On the empty index set, `extensionCoeff` is `1` in degree `0` and `0` in positive degrees. -/
@[simp]
theorem extensionCoeff_empty {ι : Type*} [DecidableEq ι] (hI : DividedPowers I) (f : A →+* B)
    (n : ℕ) (b : ι → B) (x : ι → A) :
    extensionCoeff hI f n (∅ : Finset ι) b x = if n = 0 then 1 else 0 := by
  rw [extensionCoeff_def]
  cases n with
  | zero => simp
  | succ n => simp

/-- On a singleton `{i}`, `extensionCoeff` evaluates to `b i ^ n * f (hI.dpow n (x i))`. -/
@[simp]
theorem extensionCoeff_singleton {ι : Type*} [DecidableEq ι] (hI : DividedPowers I) (f : A →+* B)
    (n : ℕ) (i : ι) (b : ι → B) (x : ι → A) :
    extensionCoeff hI f n {i} b x = b i ^ n * f (hI.dpow n (x i)) := by
  rw [extensionCoeff_def, Finset.sym_singleton, sum_singleton, prod_singleton]
  simp [Sym.replicate]

/-- In positive degree, `extensionCoeff` of elements in `I` lies in `I.map f`. -/
theorem extensionCoeff_mem {ι : Type*} [DecidableEq ι] (hI : DividedPowers I) (f : A →+* B)
    {n : ℕ} (hn : n ≠ 0) {s : Finset ι} (b : ι → B) {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) :
    extensionCoeff hI f n s b x ∈ I.map f := by
  rw [extensionCoeff_def]
  refine Submodule.sum_mem _ fun k hk ↦ ?_
  have hne : (k : Multiset ι) ≠ 0 := by
    intro h0
    have hcard := k.card_coe
    rw [h0, Multiset.card_zero] at hcard
    exact hn hcard.symm
  obtain ⟨i₀, hi₀⟩ := Multiset.exists_mem_of_ne_zero hne
  have hi₀s : i₀ ∈ s := (mem_sym_iff.mp hk) i₀ hi₀
  have hcnt : Multiset.count i₀ (k : Multiset ι) ≠ 0 :=
    Nat.ne_of_gt (Multiset.count_pos.mpr hi₀)
  rw [← mul_prod_erase s _ hi₀s]
  exact (I.map f).mul_mem_right _
    ((I.map f).mul_mem_left _ (Ideal.mem_map_of_mem f (hI.dpow_mem hcnt (hx i₀ hi₀s))))

/-- Any divided power structure `hJ` on an ideal `J` of `B` making `f` a divided power morphism
from `(I, hI)` evaluates on `∑ i ∈ s, b i * f (x i)` (`x i ∈ I`) via `extensionCoeff`. -/
theorem dpow_sum_mul_map_eq_extensionCoeff {ι : Type*} [DecidableEq ι] (hI : DividedPowers I)
    {J : Ideal B} {f : A →+* B} {hJ : DividedPowers J} (hf : IsDPMorphism hI hJ f)
    (n : ℕ) {s : Finset ι} (b : ι → B) {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) :
    hJ.dpow n (∑ i ∈ s, b i * f (x i)) = extensionCoeff hI f n s b x := by
  have hmem : ∀ i ∈ s, b i * f (x i) ∈ J := fun i hi ↦
    J.mul_mem_left _ (hf.ideal_comp (Ideal.mem_map_of_mem f (hx i hi)))
  rw [hJ.dpow_sum hmem, extensionCoeff_def]
  refine sum_congr rfl fun k _ ↦ prod_congr rfl fun i hi ↦ ?_
  rw [hJ.dpow_mul (hf.ideal_comp (Ideal.mem_map_of_mem f (hx i hi))), hf.dpow_comp (x i) (hx i hi)]

private theorem coeff_exp (hI : DividedPowers I) (n : ℕ) (x : A) :
    PowerSeries.coeff n (hI.exp x) = hI.dpow n x := by
  rw [DividedPowers.exp, PowerSeries.coeff_mk]

private theorem coeff_rescale_map_exp (hI : DividedPowers I) (f : A →+* B)
    (b : B) (n : ℕ) (x : A) :
    PowerSeries.coeff n (PowerSeries.rescale b (PowerSeries.map f (hI.exp x))) =
      b ^ n * f (hI.dpow n x) := by
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map, coeff_exp]

private theorem constantCoeff_rescale_map_exp (hI : DividedPowers I) (f : A →+* B)
    (b : B) {x : A} (hx : x ∈ I) :
    PowerSeries.constantCoeff (PowerSeries.rescale b (PowerSeries.map f (hI.exp x))) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_rescale_map_exp, pow_zero, one_mul,
    hI.dpow_zero hx, map_one]

/-- When every `x i ∈ I`, `extensionCoeff hI f n s b x` is the `n`-th coefficient of the finite
product of rescaled mapped exponentials `∏ i ∈ s, rescale (b i) (map f (hI.exp (x i)))`. -/
theorem extensionCoeff_eq_coeff_prod {ι : Type*} [DecidableEq ι] (hI : DividedPowers I)
    (f : A →+* B) (n : ℕ) {s : Finset ι} (b : ι → B) {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) :
    extensionCoeff hI f n s b x =
      PowerSeries.coeff n
        (∏ i ∈ s, PowerSeries.rescale (b i) (PowerSeries.map f (hI.exp (x i)))) := by
  let M : AddSubmonoid (Additive (PowerSeries B)) :=
    { carrier := {p | PowerSeries.constantCoeff (Additive.toMul p) = 1}
      zero_mem' := by simp
      add_mem' := fun {p q} hp hq ↦ by
        simp only [Set.mem_ofPred_eq] at hp hq ⊢
        rw [toMul_add, map_mul, hp, hq, mul_one] }
  have hM : ∀ p, p ∈ M ↔ PowerSeries.constantCoeff (Additive.toMul p) = 1 := fun _ ↦ Iff.rfl
  have hsum := DividedPowers.dpow_sum' (I := M)
    (dpow := fun k p ↦ PowerSeries.coeff k (Additive.toMul p))
    (fun {p} hp ↦ by
      rw [PowerSeries.coeff_zero_eq_constantCoeff]
      exact (hM p).mp hp)
    (fun {_ p q} _ _ ↦ by simpa using PowerSeries.coeff_mul _ (Additive.toMul p) (Additive.toMul q))
    (fun {k} hk ↦ by simp [PowerSeries.coeff_one, hk])
    (s := s)
    (x := fun i ↦ Additive.ofMul (PowerSeries.rescale (b i) (PowerSeries.map f (hI.exp (x i)))))
    (fun i hi ↦ (hM _).mpr <| by
      rw [toMul_ofMul]
      exact constantCoeff_rescale_map_exp hI f _ (hx i hi))
    (n := n)
  simp only [toMul_sum, toMul_ofMul] at hsum
  rw [hsum, extensionCoeff_def]
  refine sum_congr rfl fun k _ ↦ prod_congr rfl fun i _ ↦ ?_
  rw [coeff_rescale_map_exp]

private theorem rescale_map_exp_zero_left (hI : DividedPowers I) (f : A →+* B)
    {x : A} (hx : x ∈ I) :
    PowerSeries.rescale (0 : B) (PowerSeries.map f (hI.exp x)) = 1 := by
  ext n
  rw [coeff_rescale_map_exp, PowerSeries.coeff_one]
  cases n with
  | zero => simp [hI.dpow_zero hx]
  | succ n => simp

private theorem rescale_map_exp_add_left (hI : DividedPowers I) (f : A →+* B)
    (b₁ b₂ : B) {x : A} (hx : x ∈ I) :
    PowerSeries.rescale (b₁ + b₂) (PowerSeries.map f (hI.exp x)) =
      PowerSeries.rescale b₁ (PowerSeries.map f (hI.exp x)) *
        PowerSeries.rescale b₂ (PowerSeries.map f (hI.exp x)) := by
  ext n
  rw [coeff_rescale_map_exp, PowerSeries.coeff_mul, add_pow_mul_map_dpow hI f b₁ b₂ hx n]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [coeff_rescale_map_exp, coeff_rescale_map_exp]

private theorem rescale_map_exp_sum_left {κ : Type*} (hI : DividedPowers I) (f : A →+* B)
    (t : Finset κ) (c : κ → B) {x : A} (hx : x ∈ I) :
    PowerSeries.rescale (∑ j ∈ t, c j) (PowerSeries.map f (hI.exp x)) =
      ∏ j ∈ t, PowerSeries.rescale (c j) (PowerSeries.map f (hI.exp x)) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using rescale_map_exp_zero_left hI f hx
  | insert j t hj ih =>
    rw [sum_insert hj, prod_insert hj, rescale_map_exp_add_left hI f _ _ hx, ih]

private theorem rescale_map_exp_zero_right (hI : DividedPowers I) (f : A →+* B) (b : B) :
    PowerSeries.rescale b (PowerSeries.map f (hI.exp 0)) = 1 := by
  ext n
  rw [coeff_rescale_map_exp, PowerSeries.coeff_one]
  cases n with
  | zero => simp [hI.dpow_zero I.zero_mem]
  | succ n => simp [hI.dpow_eval_zero (Nat.succ_ne_zero n)]

private theorem rescale_map_exp_sum_right {ι : Type*} (hI : DividedPowers I) (f : A →+* B)
    (s : Finset ι) (b : B) (x : ι → A) (hx : ∀ i ∈ s, x i ∈ I) :
    PowerSeries.rescale b (PowerSeries.map f (hI.exp (∑ i ∈ s, x i))) =
      ∏ i ∈ s, PowerSeries.rescale b (PowerSeries.map f (hI.exp (x i))) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using rescale_map_exp_zero_right hI f b
  | insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi,
      hI.exp_add (hx i (mem_insert_self i s))
        (Submodule.sum_mem _ fun k hk ↦ hx k (mem_insert_of_mem hk)),
      map_mul, map_mul, ih fun k hk ↦ hx k (mem_insert_of_mem hk)]

private theorem rescale_map_exp_mul_map (hI : DividedPowers I) (f : A →+* B)
    (a : A) (c : B) {x : A} (hx : x ∈ I) :
    PowerSeries.rescale (f a * c) (PowerSeries.map f (hI.exp x)) =
      PowerSeries.rescale c (PowerSeries.map f (hI.exp (a * x))) := by
  ext n
  simp only [coeff_rescale_map_exp, hI.dpow_mul hx, map_mul, map_pow, mul_pow]
  ring

/-- **Invariance under finite scalar substitution** (Stacks 23.4.2, tag 07H1): replacing
`b i = ∑ j ∈ t, f (a i j) * c j` by `c j` and `x i` by `y j = ∑ i ∈ s, a i j * x i` leaves
`extensionCoeff` unchanged, without any flatness hypothesis. -/
theorem extensionCoeff_subst {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (hI : DividedPowers I) (f : A →+* B) (n : ℕ) (s : Finset ι) (t : Finset κ)
    (a : ι → κ → A) (c : κ → B) {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) :
    extensionCoeff hI f n s (fun i ↦ ∑ j ∈ t, f (a i j) * c j) x =
      extensionCoeff hI f n t c (fun j ↦ ∑ i ∈ s, a i j * x i) := by
  have hy : ∀ j ∈ t, (∑ i ∈ s, a i j * x i) ∈ I := fun j _ ↦
    Submodule.sum_mem _ fun i hi ↦ I.mul_mem_left (a i j) (hx i hi)
  rw [extensionCoeff_eq_coeff_prod hI f n _ hx, extensionCoeff_eq_coeff_prod hI f n _ hy]
  congr 1
  calc ∏ i ∈ s, PowerSeries.rescale (∑ j ∈ t, f (a i j) * c j) (PowerSeries.map f (hI.exp (x i)))
      = ∏ i ∈ s, ∏ j ∈ t, PowerSeries.rescale (f (a i j) * c j)
          (PowerSeries.map f (hI.exp (x i))) :=
        prod_congr rfl fun i hi ↦ rescale_map_exp_sum_left hI f t _ (hx i hi)
    _ = ∏ i ∈ s, ∏ j ∈ t, PowerSeries.rescale (c j)
          (PowerSeries.map f (hI.exp (a i j * x i))) :=
        prod_congr rfl fun i hi ↦ prod_congr rfl fun j _ ↦
          rescale_map_exp_mul_map hI f (a i j) (c j) (hx i hi)
    _ = ∏ j ∈ t, ∏ i ∈ s, PowerSeries.rescale (c j)
          (PowerSeries.map f (hI.exp (a i j * x i))) := prod_comm
    _ = ∏ j ∈ t, PowerSeries.rescale (c j)
          (PowerSeries.map f (hI.exp (∑ i ∈ s, a i j * x i))) :=
        prod_congr rfl fun j _ ↦
          (rescale_map_exp_sum_right hI f s (c j) _ fun i hi ↦ I.mul_mem_left _ (hx i hi)).symm

end ExtensionCoeff

section FlatExtension

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {I : Ideal A}

/-- **Independence of the presentation over a flat algebra** (Stacks 23.4.2, tag 07H1): if `B` is
flat over `A` and two finite `B`-linear combinations of elements of `I` have the same sum in `B`,
then their `extensionCoeff` values agree in every degree. -/
theorem extensionCoeff_eq_of_sum_eq [Module.Flat A B] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (hI : DividedPowers I) (n : ℕ) {s : Finset ι} {t : Finset κ}
    {b : ι → B} {b' : κ → B} {x : ι → A} {x' : κ → A}
    (hx : ∀ i ∈ s, x i ∈ I) (hx' : ∀ j ∈ t, x' j ∈ I)
    (hsum : ∑ i ∈ s, b i * algebraMap A B (x i) = ∑ j ∈ t, b' j * algebraMap A B (x' j)) :
    extensionCoeff hI (algebraMap A B) n s b x = extensionCoeff hI (algebraMap A B) n t b' x' := by
  let r : s ⊕ t → A := Sum.elim (fun i ↦ x i) (fun j ↦ -(x' j))
  let m : s ⊕ t → B := Sum.elim (fun i ↦ b i) (fun j ↦ b' j)
  have hrel : ∑ u : s ⊕ t, r u • m u = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [r, m, Sum.elim_inl, Sum.elim_inr, Algebra.smul_def, map_neg, neg_mul,
      sum_neg_distrib, mul_comm (algebraMap A B _)]
    rw [sum_coe_sort s (fun i ↦ b i * algebraMap A B (x i)),
      sum_coe_sort t (fun j ↦ b' j * algebraMap A B (x' j)), hsum, add_neg_cancel]
  obtain ⟨l, a, c, hm, hr⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  let a₁ : ι → Fin l → A := fun i k ↦ if hi : i ∈ s then a (.inl ⟨i, hi⟩) k else 0
  let a₂ : κ → Fin l → A := fun j k ↦ if hj : j ∈ t then a (.inr ⟨j, hj⟩) k else 0
  have hb₁ : ∀ i ∈ s, b i = ∑ k : Fin l, algebraMap A B (a₁ i k) * c k := fun i hi ↦ by
    simpa only [m, a₁, Sum.elim_inl, dite_eq_left hi, Algebra.smul_def] using hm (.inl ⟨i, hi⟩)
  have hb₂ : ∀ j ∈ t, b' j = ∑ k : Fin l, algebraMap A B (a₂ j k) * c k := fun j hj ↦ by
    simpa only [m, a₂, Sum.elim_inr, dite_eq_left hj, Algebra.smul_def] using hm (.inr ⟨j, hj⟩)
  have hy_eq : ∀ k : Fin l, ∑ i ∈ s, a₁ i k * x i = ∑ j ∈ t, a₂ j k * x' j := fun k ↦ by
    have hk := hr k
    rw [Fintype.sum_sum_type] at hk
    simp only [r, Sum.elim_inl, Sum.elim_inr, neg_mul, sum_neg_distrib] at hk
    have h1 : ∑ i : s, x i * a (.inl i) k = ∑ i ∈ s, a₁ i k * x i := by
      rw [← sum_coe_sort s (fun i ↦ a₁ i k * x i)]
      exact sum_congr rfl fun i _ ↦ by simp only [a₁, dite_eq_left i.2, mul_comm]
    have h2 : ∑ j : t, x' j * a (.inr j) k = ∑ j ∈ t, a₂ j k * x' j := by
      rw [← sum_coe_sort t (fun j ↦ a₂ j k * x' j)]
      exact sum_congr rfl fun j _ ↦ by simp only [a₂, dite_eq_left j.2, mul_comm]
    rw [h1, h2] at hk
    exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hk)
  rw [extensionCoeff_congr hI (algebraMap A B) n hb₁ (fun _ _ ↦ rfl),
    extensionCoeff_congr hI (algebraMap A B) n hb₂ (fun _ _ ↦ rfl),
    extensionCoeff_subst hI (algebraMap A B) n s univ a₁ c hx,
    extensionCoeff_subst hI (algebraMap A B) n t univ a₂ c hx']
  simp_rw [hy_eq]

private theorem exists_sum_mul_algebraMap_of_mem_map {B : Type*} [CommRing B] [Algebra A B]
    {z : B} (hz : z ∈ I.map (algebraMap A B)) :
    ∃ (t : Finset A), (t : Set A) ⊆ I ∧ ∃ (c : t → B),
      (∑ i : t, c i * algebraMap A B i) = z := by
  rw [Ideal.map, Submodule.mem_span_image_iff_exists_fun] at hz
  obtain ⟨t, ht, c, rfl⟩ := hz
  exact ⟨t, ht, c, by simp only [smul_eq_mul]⟩

private noncomputable def flatDpow (hI : DividedPowers I) (B : Type*) [CommRing B] [Algebra A B]
    (n : ℕ) (z : B) : B :=
  open scoped Classical in
  if hz : z ∈ I.map (algebraMap A B) then
    let h := exists_sum_mul_algebraMap_of_mem_map hz
    extensionCoeff hI (algebraMap A B) n univ h.choose_spec.2.choose Subtype.val
  else 0

private theorem flatDpow_sum [Module.Flat A B] {ι : Type*} [DecidableEq ι] (hI : DividedPowers I)
    (n : ℕ) {s : Finset ι} (b : ι → B) {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) :
    flatDpow hI B n (∑ i ∈ s, b i * algebraMap A B (x i)) =
      extensionCoeff hI (algebraMap A B) n s b x := by
  classical
  have hz : ∑ i ∈ s, b i * algebraMap A B (x i) ∈ I.map (algebraMap A B) :=
    Submodule.sum_mem _ fun i hi ↦
      (I.map (algebraMap A B)).mul_mem_left _ (Ideal.mem_map_of_mem _ (hx i hi))
  simp only [flatDpow, dite_eq_left hz]
  set h := exists_sum_mul_algebraMap_of_mem_map hz
  exact extensionCoeff_eq_of_sum_eq hI n
    (fun i _ ↦ h.choose_spec.1 i.2) hx h.choose_spec.2.choose_spec

private theorem flatDpow_sum_eq_coeff_prod [Module.Flat A B] {ι : Type*}
    (hI : DividedPowers I) (n : ℕ) {s : Finset ι} (b : ι → B) {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) :
    flatDpow hI B n (∑ i ∈ s, b i * algebraMap A B (x i)) =
      PowerSeries.coeff n
        (∏ i ∈ s, PowerSeries.rescale (b i) (PowerSeries.map (algebraMap A B) (hI.exp (x i)))) := by
  classical
  exact (flatDpow_sum hI n b hx).trans (extensionCoeff_eq_coeff_prod hI (algebraMap A B) n b hx)

private noncomputable def flatAdditivePowers (hI : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] :
    AdditivePowers (I.map (algebraMap A B)) where
  dpow := flatDpow hI B
  dpow_null {n z} hz := by
    classical
    simp [flatDpow, hz]
  dpow_zero {z} hz := by
    classical
    obtain ⟨t, ht, c, rfl⟩ := exists_sum_mul_algebraMap_of_mem_map hz
    rw [flatDpow_sum_eq_coeff_prod hI 0 c (fun i _ ↦ ht i.2),
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod]
    exact prod_eq_one fun i _ ↦ constantCoeff_rescale_map_exp hI (algebraMap A B) _ (ht i.2)
  dpow_one {z} hz := by
    classical
    obtain ⟨t, ht, c, rfl⟩ := exists_sum_mul_algebraMap_of_mem_map hz
    rw [flatDpow_sum_eq_coeff_prod hI 1 c (fun i _ ↦ ht i.2), PowerSeries.coeff_one_prod]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [prod_eq_one fun j _ ↦ constantCoeff_rescale_map_exp hI (algebraMap A B) _ (ht j.2),
      mul_one, coeff_rescale_map_exp, pow_one, hI.dpow_one (ht i.2)]
  dpow_mem {n z} hn hz := by
    classical
    obtain ⟨t, ht, c, rfl⟩ := exists_sum_mul_algebraMap_of_mem_map hz
    rw [flatDpow_sum hI n c (fun i _ ↦ ht i.2)]
    exact extensionCoeff_mem hI (algebraMap A B) hn c (fun i _ ↦ ht i.2)
  dpow_add {n z₁ z₂} hz₁ hz₂ := by
    classical
    obtain ⟨t₁, ht₁, c₁, rfl⟩ := exists_sum_mul_algebraMap_of_mem_map hz₁
    obtain ⟨t₂, ht₂, c₂, rfl⟩ := exists_sum_mul_algebraMap_of_mem_map hz₂
    have hsum : (∑ i : t₁, c₁ i * algebraMap A B i) + (∑ j : t₂, c₂ j * algebraMap A B j) =
        ∑ u : t₁ ⊕ t₂, Sum.elim c₁ c₂ u * algebraMap A B (Sum.elim Subtype.val Subtype.val u) := by
      rw [Fintype.sum_sum_type]
      simp
    have hx₁₂ : ∀ u ∈ (univ : Finset (t₁ ⊕ t₂)), Sum.elim Subtype.val Subtype.val u ∈ I :=
      fun u _ ↦ by cases u with | inl i => exact ht₁ i.2 | inr j => exact ht₂ j.2
    rw [hsum, flatDpow_sum_eq_coeff_prod hI n (Sum.elim c₁ c₂) hx₁₂, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [PowerSeries.coeff_mul]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [flatDpow_sum_eq_coeff_prod hI k.1 c₁ (fun i _ ↦ ht₁ i.2),
      flatDpow_sum_eq_coeff_prod hI k.2 c₂ (fun j _ ↦ ht₂ j.2)]
  dpow_mul {n a z} hz := by
    classical
    obtain ⟨t, ht, c, rfl⟩ := exists_sum_mul_algebraMap_of_mem_map hz
    have hmul : a * ∑ i : t, c i * algebraMap A B i =
        ∑ i : t, (a * c i) * algebraMap A B i := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ (mul_assoc _ _ _).symm
    rw [hmul, flatDpow_sum_eq_coeff_prod hI n (fun i ↦ a * c i) (fun i _ ↦ ht i.2),
      flatDpow_sum_eq_coeff_prod hI n c (fun i _ ↦ ht i.2)]
    have hprod : ∏ i : t, PowerSeries.rescale (a * c i)
          (PowerSeries.map (algebraMap A B) (hI.exp i)) =
        PowerSeries.rescale a (∏ i : t, PowerSeries.rescale (c i)
          (PowerSeries.map (algebraMap A B) (hI.exp i))) := by
      rw [map_prod]
      exact prod_congr rfl fun i _ ↦ by rw [mul_comm a (c i), PowerSeries.rescale_rescale]
    rw [hprod, PowerSeries.coeff_rescale]

private theorem flatAdditivePowers_dpow_algebraMap [Module.Flat A B] (hI : DividedPowers I)
    (n : ℕ) {x : A} (hx : x ∈ I) :
    (flatAdditivePowers hI B).dpow n (algebraMap A B x) = algebraMap A B (hI.dpow n x) := by
  dsimp only [flatAdditivePowers]
  have h := flatDpow_sum (B := B) hI n (s := {()}) (fun _ ↦ (1 : B)) (x := fun _ ↦ x)
    (fun _ _ ↦ hx)
  simpa only [sum_singleton, one_mul, extensionCoeff_singleton, one_pow] using h

/-- **Flat extension of divided powers** (Stacks 23.4.2, tag 07H1, condition (3)): if `B` is a flat
`A`-algebra, then `hI` extends uniquely to a divided power structure on `I.map (algebraMap A B)`. -/
noncomputable def mapOfFlat (hI : DividedPowers I) (B : Type*) [CommRing B] [Algebra A B]
    [Module.Flat A B] :
    DividedPowers (I.map (algebraMap A B)) :=
  (flatAdditivePowers hI B).toDividedPowers (S := algebraMap A B '' (I : Set A))
    (by rw [Ideal.map])
    (fun s hs m n ↦ by
      obtain ⟨x, hx, rfl⟩ := hs
      simp only [flatAdditivePowers_dpow_algebraMap hI _ hx]
      rw [← map_mul, hI.mul_dpow hx, map_mul, map_natCast])
    (fun s hs m {n} hn ↦ by
      obtain ⟨x, hx, rfl⟩ := hs
      simp only [flatAdditivePowers_dpow_algebraMap hI _ hx,
        flatAdditivePowers_dpow_algebraMap hI _ (hI.dpow_mem hn hx)]
      rw [hI.dpow_comp hn hx, map_mul, map_natCast])

/-- On any finite `B`-linear combination `∑ i ∈ s, b i * algebraMap A B (x i)` with `x i ∈ I`,
`mapOfFlat` evaluates via `extensionCoeff`. -/
theorem mapOfFlat_dpow_sum [Module.Flat A B] {ι : Type*} [DecidableEq ι] (hI : DividedPowers I)
    (n : ℕ) {s : Finset ι} (b : ι → B) {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) :
    (hI.mapOfFlat B).dpow n (∑ i ∈ s, b i * algebraMap A B (x i)) =
      extensionCoeff hI (algebraMap A B) n s b x := by
  rw [mapOfFlat, AdditivePowers.toDividedPowers_dpow]
  exact flatDpow_sum hI n b hx

/-- `algebraMap A B` is a divided power morphism from `(I, hI)` to
`(I.map (algebraMap A B), hI.mapOfFlat B)`. -/
theorem isDPMorphism_mapOfFlat [Module.Flat A B] (hI : DividedPowers I) :
    IsDPMorphism hI (hI.mapOfFlat B) (algebraMap A B) where
  ideal_comp := le_rfl
  dpow_comp {n} x hx := by
    rw [mapOfFlat, AdditivePowers.toDividedPowers_dpow]
    exact flatAdditivePowers_dpow_algebraMap hI n hx

/-- On an element `algebraMap A B x` with `x ∈ I`, `mapOfFlat` agrees with `hI`. -/
@[simp]
theorem mapOfFlat_dpow_algebraMap [Module.Flat A B] (hI : DividedPowers I)
    (n : ℕ) {x : A} (hx : x ∈ I) :
    (hI.mapOfFlat B).dpow n (algebraMap A B x) = algebraMap A B (hI.dpow n x) :=
  (isDPMorphism_mapOfFlat hI).dpow_comp x hx

/-- On a scalar multiple `b * algebraMap A B x` with `x ∈ I`, `mapOfFlat` evaluates to
`b ^ n * algebraMap A B (hI.dpow n x)`. -/
theorem mapOfFlat_dpow_mul [Module.Flat A B] (hI : DividedPowers I)
    (n : ℕ) (b : B) {x : A} (hx : x ∈ I) :
    (hI.mapOfFlat B).dpow n (b * algebraMap A B x) = b ^ n * algebraMap A B (hI.dpow n x) := by
  rw [(hI.mapOfFlat B).dpow_mul (Ideal.mem_map_of_mem _ hx), mapOfFlat_dpow_algebraMap hI n hx]

/-- Uniqueness of `DividedPowers.mapOfFlat`: a divided power structure on `I.map (algebraMap A B)`
equals `hI.mapOfFlat B` if and only if `algebraMap A B` is a divided power morphism into it. -/
theorem eq_mapOfFlat_iff [Module.Flat A B] (hI : DividedPowers I)
    (hB : DividedPowers (I.map (algebraMap A B))) :
    hB = hI.mapOfFlat B ↔ IsDPMorphism hI hB (algebraMap A B) :=
  ⟨fun h ↦ h ▸ isDPMorphism_mapOfFlat hI,
    fun hf ↦ ext_of_isDPMorphism_map hI (algebraMap A B) hf (isDPMorphism_mapOfFlat hI)⟩

/-- Universal property of `DividedPowers.mapOfFlat`: a ring homomorphism `g : B →+* C` is a divided
power morphism out of `(I.map (algebraMap A B), hI.mapOfFlat B)` if and only if
`g.comp (algebraMap A B)` is a divided power morphism out of `(I, hI)`. -/
theorem isDPMorphism_mapOfFlat_iff [Module.Flat A B] {C : Type*} [CommSemiring C] {K : Ideal C}
    (hI : DividedPowers I) (hK : DividedPowers K) (g : B →+* C) :
    IsDPMorphism (hI.mapOfFlat B) hK g ↔ IsDPMorphism hI hK (g.comp (algebraMap A B)) :=
  isDPMorphism_comp_iff_of_map hI (isDPMorphism_mapOfFlat hI) hK g

/-- Transitivity of flat extension for a tower of flat algebras `A → B → C`. -/
theorem mapOfFlat_comp_dpow {C : Type*} [CommRing C] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [Module.Flat A B] [Module.Flat B C]
    (hI : DividedPowers I) (n : ℕ) (c : C) :
    have : Module.Flat A C := Module.Flat.trans A B C
    ((hI.mapOfFlat B).mapOfFlat C).dpow n c = (hI.mapOfFlat C).dpow n c := by
  have : Module.Flat A C := Module.Flat.trans A B C
  have hId : (I.map (algebraMap A B)).map (algebraMap B C) = I.map (algebraMap A C) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A B C]
  have hcomp : IsDPMorphism hI ((hI.mapOfFlat B).mapOfFlat C) (algebraMap A C) := by
    rw [IsScalarTower.algebraMap_eq A B C]
    exact (isDPMorphism_mapOfFlat (hI.mapOfFlat B)).comp _ (isDPMorphism_mapOfFlat hI)
  have hcomp' : IsDPMorphism hI (hId ▸ (hI.mapOfFlat B).mapOfFlat C) (algebraMap A C) := by
    have aux : ∀ {J K : Ideal C} (h : J = K) (hJ : DividedPowers J),
        IsDPMorphism hI hJ (algebraMap A C) → IsDPMorphism hI (h ▸ hJ) (algebraMap A C) := by
      rintro J _ rfl hJ hD; exact hD
    exact aux hId ((hI.mapOfFlat B).mapOfFlat C) hcomp
  have heq : hId ▸ (hI.mapOfFlat B).mapOfFlat C = hI.mapOfFlat C :=
    ext_of_isDPMorphism_map hI (algebraMap A C) hcomp' (isDPMorphism_mapOfFlat hI)
  have hdpow : ∀ {J K : Ideal C} (h : J = K) (hJ : DividedPowers J),
      (h ▸ hJ).dpow n c = hJ.dpow n c := by
    rintro J _ rfl hJ; rfl
  rw [← hdpow hId ((hI.mapOfFlat B).mapOfFlat C), heq]

/-- When `algebraMap A B` comes from a ring equivalence `e : A ≃+* B`, `mapOfFlat` coincides with
Mathlib's `DividedPowers.ofRingEquiv`. -/
theorem mapOfFlat_eq_ofRingEquiv [Module.Flat A B] (hI : DividedPowers I)
    (e : A ≃+* B) (he : (e : A →+* B) = algebraMap A B) :
    hI.mapOfFlat B = hI.ofRingEquiv (e := e) (by rw [← he]; rfl) := by
  symm
  rw [eq_mapOfFlat_iff]
  refine ⟨le_rfl, fun {n} a _ ↦ ?_⟩
  have ha : ∀ x : A, algebraMap A B x = e x := fun x ↦ by rw [← he]; rfl
  rw [ha a, ha (hI.dpow n a), DividedPowers.ofRingEquiv_dpow_apply]

/-- When `I = Ideal.span {x}` is principal, `mapOfFlat` coincides with `mapOfSpanSingleton`. -/
theorem mapOfFlat_eq_mapOfSpanSingleton [Module.Flat A B] (hI : DividedPowers I)
    {x : A} (hIx : I = Ideal.span {x}) :
    hI.mapOfFlat B = hI.mapOfSpanSingleton (algebraMap A B) hIx :=
  ext_of_isDPMorphism_map hI (algebraMap A B) (isDPMorphism_mapOfFlat hI)
    (isDPMorphism_mapOfSpanSingleton hI (algebraMap A B) hIx)

end FlatExtension

section Localization

variable {A : Type*} [CommRing A] {I : Ideal A}

/-- **Divided powers after localization** (Stacks 23.4.2, tag 07H1): for any submonoid `S` of `A`
and localization `B` of `A` at `S`, `hI` extends uniquely to `I.map (algebraMap A B)`. -/
noncomputable def mapOfIsLocalization (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommRing B] [Algebra A B] [IsLocalization S B] :
    DividedPowers (I.map (algebraMap A B)) :=
  have : Module.Flat A B := IsLocalization.flat B S
  hI.mapOfFlat B

/-- `mapOfIsLocalization` agrees definitionally with `mapOfFlat` when `[Module.Flat A B]` is in
scope. -/
theorem mapOfIsLocalization_eq_mapOfFlat (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommRing B] [Algebra A B] [IsLocalization S B] [Module.Flat A B] :
    hI.mapOfIsLocalization S B = hI.mapOfFlat B := (rfl)

/-- The localization map `algebraMap A B` is a divided power morphism from `(I, hI)` to
`(I.map (algebraMap A B), hI.mapOfIsLocalization S B)`. -/
theorem isDPMorphism_mapOfIsLocalization (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommRing B] [Algebra A B] [IsLocalization S B] :
    IsDPMorphism hI (hI.mapOfIsLocalization S B) (algebraMap A B) := by
  have : Module.Flat A B := IsLocalization.flat B S
  rw [mapOfIsLocalization_eq_mapOfFlat]
  exact isDPMorphism_mapOfFlat hI

/-- On `algebraMap A B x` with `x ∈ I`, `mapOfIsLocalization` agrees with `hI`. -/
@[simp]
theorem mapOfIsLocalization_dpow_algebraMap (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommRing B] [Algebra A B] [IsLocalization S B] (n : ℕ) {x : A} (hx : x ∈ I) :
    (hI.mapOfIsLocalization S B).dpow n (algebraMap A B x) = algebraMap A B (hI.dpow n x) :=
  (isDPMorphism_mapOfIsLocalization hI S B).dpow_comp x hx

/-- Uniqueness of `DividedPowers.mapOfIsLocalization`: a divided power structure on
`I.map (algebraMap A B)` equals `hI.mapOfIsLocalization S B` if and only if `algebraMap A B` is a
divided power morphism into it. -/
theorem eq_mapOfIsLocalization_iff (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommRing B] [Algebra A B] [IsLocalization S B] (hB : DividedPowers (I.map (algebraMap A B))) :
    hB = hI.mapOfIsLocalization S B ↔ IsDPMorphism hI hB (algebraMap A B) := by
  have : Module.Flat A B := IsLocalization.flat B S
  rw [mapOfIsLocalization_eq_mapOfFlat]
  exact eq_mapOfFlat_iff hI hB

/-- Universal property of `DividedPowers.mapOfIsLocalization` for outgoing divided power
morphisms. -/
theorem isDPMorphism_mapOfIsLocalization_iff {C : Type*} [CommSemiring C] {K : Ideal C}
    (hI : DividedPowers I) (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization S B] (hK : DividedPowers K) (g : B →+* C) :
    IsDPMorphism (hI.mapOfIsLocalization S B) hK g ↔
      IsDPMorphism hI hK (g.comp (algebraMap A B)) :=
  isDPMorphism_comp_iff_of_map hI (isDPMorphism_mapOfIsLocalization hI S B) hK g

/-- **Fraction formula for localized divided powers**: on `x / s` with `x ∈ I` and `s ∈ S`, the
`n`-th divided power is `hI.dpow n x / s ^ n`. -/
@[simp]
theorem mapOfIsLocalization_dpow_mk' (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommRing B] [Algebra A B] [IsLocalization S B] (n : ℕ) {x : A} (hx : x ∈ I) (s : S) :
    (hI.mapOfIsLocalization S B).dpow n (IsLocalization.mk' B x s) =
      IsLocalization.mk' B (hI.dpow n x) (s ^ n) := by
  have : Module.Flat A B := IsLocalization.flat B S
  rw [mapOfIsLocalization_eq_mapOfFlat, IsLocalization.mk'_eq_mul_mk'_one, mul_comm,
    mapOfFlat_dpow_mul hI n _ hx, ← IsLocalization.mk'_pow, one_pow, mul_comm,
    ← IsLocalization.mk'_eq_mul_mk'_one]

end Localization

end DividedPowers
