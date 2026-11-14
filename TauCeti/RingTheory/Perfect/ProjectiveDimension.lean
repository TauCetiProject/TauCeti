/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import TauCeti.Algebra.Category.ModuleCat.Projective.SequentialColimit
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.RingTheory.Perfect.IsPRadical
import TauCeti.RingTheory.Perfect.PerfectClosure
import TauCeti.RingTheory.Perfect.Tor
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.RegularLocalRing.Frobenius

/-!
# Projective dimension over perfect closures and their perfect quotients

Let `K` be a ring of exponential characteristic `p` whose Frobenius endomorphism is flat, and
suppose that every `K`-module has projective dimension at most `d`. Then every module over a
perfect closure `i : K →+* L`, for instance Mathlib's colimit perfection `PerfectClosure K p`, has
projective dimension at most `d + 1`. By Kunz's theorem this applies to a regular ring `K` of
Krull dimension at most `d`, whose Frobenius is flat and whose modules have projective dimension
at most `d`: the perfection of a regular ring of finite Krull dimension has finite global
dimension.

The perfect closure `L` is the union of the increasing sequence of subrings `i(K) ^ (1 / p ^ n)`,
the images of `x ↦ i(x) ^ (1 / p ^ n)`. Each of them is isomorphic to `K` because `i` is
injective: its kernel is the `p`-nilradical of `K`, which vanishes because flat Frobenius is
injective. The perfect closure is flat over each of them because it is flat over `K`
(`RingHom.Flat.of_isPerfectClosure`). Every module over `L` is then the colimit of its base
changes from these subrings, which have projective dimension at most `d`, and the telescope
sequence adds one (`ModuleCat.hasProjectiveDimensionLT_succ_of_iSup_eq_top`).

Furthermore, if `φ : P →+* R` is a surjective homomorphism from a perfect ring `P` of prime
characteristic `p` onto a reduced (equivalently, perfect) ring `R`, then `Tor_n^P(R, M) = 0` for
every `R`-module `M` and every `n > 0` (`TauCeti.isZero_Tor_succ_of_surjective_of_isReduced`). Base
change `R ⊗[P] -` therefore carries any projective resolution of `M` over `P` to a projective
resolution of `R ⊗[P] M ≅ M` over `R`, so the projective dimension of `M` over `R` is at most its
projective dimension over `P` (`RingHom.hasProjectiveDimensionLE_of_surjective_of_isReduced`). In
particular, over any reduced quotient of a perfect closure `L` of a regular ring `K` of Krull
dimension at most `d`, every module has projective dimension at most `d + 1`; more generally, over
any reduced quotient of the perfect polynomial algebra `PerfectClosure (MvPolynomial σ L) p` on a
finite set `σ` (a perfectly finitely presented `L`-algebra), every module has projective dimension
at most `d + Nat.card σ + 1` (Bhatt and Scholze, Proposition 11.31).

## Main results

* `RingHom.hasProjectiveDimensionLE_of_surjective_of_isReduced` and
  `RingHom.projectiveDimension_le_of_surjective_of_isReduced`: along a surjection `φ : P →+* R`
  from a perfect ring of prime characteristic onto a reduced ring, projective dimension over `R` is
  bounded by projective dimension over `P`.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ`: if Frobenius of `K` is flat and every
  `K`-module has projective dimension at most `d`, then every module over a perfect closure of
  `K` has projective dimension at most `d + 1`.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing`: over a perfect closure of a
  regular ring of Krull dimension at most `d`, every module has projective dimension at most
  `d + 1`.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ_of_surjective_of_isRegularRing`: the same `d + 1`
  bound over any reduced (or perfect) quotient of a perfect closure of a regular ring of Krull
  dimension at most `d`.
* `IsPRadical.hasProjectiveDimensionLE_perfectClosure_mvPolynomial_of_surjective`: **Bhatt
  and Scholze, Proposition 11.31**, every module over a perfectly finitely presented algebra on a
  finite generator set `σ` over a `p`-radical extension (in particular, a perfect closure) of a
  regular ring of Krull dimension at most `d` has projective dimension at most
  `d + Nat.card σ + 1`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Proposition 11.31 and its proof.
* E. Kunz, *Characterizations of regular local rings of characteristic p*, Amer. J. Math. 91
  (1969), 772–784.
-/

public section

open CategoryTheory

universe u

namespace RingHom

variable {P R : Type u} [CommRing P] [CommRing R] (p : ℕ) [Fact p.Prime] [ExpChar P p]
  [PerfectRing P p]

include p

/-- Along a surjective homomorphism `φ : P →+* R` from a perfect ring of prime characteristic `p`
onto a reduced ring `R`, an `R`-module `M` has projective dimension at most `m` over `R` whenever
its restriction of scalars has projective dimension at most `m` over `P`. -/
theorem hasProjectiveDimensionLE_of_surjective_of_isReduced [IsReduced R] {φ : P →+* R}
    (hφ : Function.Surjective φ) {M : ModuleCat.{u} R} {m : ℕ}
    (hM : HasProjectiveDimensionLE ((ModuleCat.restrictScalars φ).obj M) m) :
    HasProjectiveDimensionLE M m :=
  ModuleCat.hasProjectiveDimensionLE_of_surjective_of_isZero_Tor φ hφ
    (TauCeti.isZero_Tor_succ_of_surjective_of_isReduced p hφ M) hM

/-- Along a surjective homomorphism `φ : P →+* R` from a perfect ring of prime characteristic `p`
onto a reduced ring `R`, projective dimension over `R` is bounded by projective dimension over
`P`. -/
theorem projectiveDimension_le_of_surjective_of_isReduced [IsReduced R] {φ : P →+* R}
    (hφ : Function.Surjective φ) (M : ModuleCat.{u} R) :
    projectiveDimension M ≤ projectiveDimension ((ModuleCat.restrictScalars φ).obj M) :=
  ModuleCat.projectiveDimension_le_of_surjective_of_isZero_Tor φ hφ
    (TauCeti.isZero_Tor_succ_of_surjective_of_isReduced p hφ M)

/-- Specialization of `RingHom.hasProjectiveDimensionLE_of_surjective_of_isReduced` to a perfect
target ring. -/
theorem hasProjectiveDimensionLE_of_surjective_of_perfectRing [PerfectRing R p] {φ : P →+* R}
    (hφ : Function.Surjective φ) {M : ModuleCat.{u} R} {m : ℕ}
    (hM : HasProjectiveDimensionLE ((ModuleCat.restrictScalars φ).obj M) m) :
    HasProjectiveDimensionLE M m := by
  have := TauCeti.isReduced_of_perfectRing R p
  exact φ.hasProjectiveDimensionLE_of_surjective_of_isReduced p hφ hM

/-- Specialization of `RingHom.projectiveDimension_le_of_surjective_of_isReduced` to a perfect
target ring. -/
theorem projectiveDimension_le_of_surjective_of_perfectRing [PerfectRing R p] {φ : P →+* R}
    (hφ : Function.Surjective φ) (M : ModuleCat.{u} R) :
    projectiveDimension M ≤ projectiveDimension ((ModuleCat.restrictScalars φ).obj M) := by
  have := TauCeti.isReduced_of_perfectRing R p
  exact φ.projectiveDimension_le_of_surjective_of_isReduced p hφ M

end RingHom

namespace IsPerfectClosure

variable {K L : Type u} [CommRing K] [CommRing L] (i : K →+* L) (p : ℕ) [ExpChar L p]
  [PerfectRing L p]

/-- The `n`-th stage `x ↦ i(x) ^ (1 / p ^ n)` of the perfect closure `i`. -/
private noncomputable def stage (n : ℕ) : K →+* L :=
  (iterateFrobeniusEquiv L p n).symm.toRingHom.comp i

/-- The images of the stages increase: `i(x) ^ (1 / p ^ n) = i(x ^ p) ^ (1 / p ^ (n + 1))`. -/
private theorem monotone_range_stage : Monotone fun n ↦ (stage i p n).range :=
  monotone_nat_of_le_succ fun n ↦ by
    rintro _ ⟨x, rfl⟩
    refine ⟨x ^ p, (iterateFrobeniusEquiv L p (n + 1)).injective ?_⟩
    simp only [stage, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply, map_pow]
    rw [add_comm n 1, iterateFrobeniusEquiv_add_apply, RingEquiv.apply_symm_apply,
      iterateFrobeniusEquiv_one_apply]

variable [IsPerfectClosure i p]

/-- Every element of a perfect closure is `i(x) ^ (1 / p ^ n)` for some `x` and `n`. -/
private theorem iSup_range_stage : ⨆ n, (stage i p n).range = ⊤ :=
  eq_top_iff.2 fun x _ ↦ by
    obtain ⟨n, y, hy⟩ := IsPRadical.pow_mem i p x
    refine le_iSup (fun n ↦ (stage i p n).range) n ⟨y, ?_⟩
    rw [stage, RingHom.comp_apply, hy, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_eq, iterateFrobeniusEquiv_def]

variable [ExpChar K p]

/-- The stages are injective when Frobenius is flat: the kernel of `i` is the `p`-nilradical,
which vanishes because flat Frobenius is injective. -/
private theorem stage_injective (hF : (frobenius K p).Flat) (n : ℕ) :
    Function.Injective (stage i p n) :=
  (iterateFrobeniusEquiv L p n).symm.injective.comp (injective_of_flat_frobenius i p hF)

/-- When Frobenius is flat, the `n`-th stage identifies `K` with its image. -/
private noncomputable def stageEquiv (hF : (frobenius K p).Flat) (n : ℕ) :
    K ≃+* (stage i p n).range :=
  RingEquiv.ofBijective (stage i p n).rangeRestrict
    ⟨fun _ _ h ↦ stage_injective i p hF n congr($h.1), (stage i p n).rangeRestrict_surjective⟩

/-- A perfect closure is flat over the image of each stage. -/
private theorem flat_range_stage (hF : (frobenius K p).Flat) (n : ℕ) :
    Module.Flat (stage i p n).range L := by
  rw [← RingHom.flat_algebraMap_iff, ← RingHom.Flat.comp_iff_of_bijective_right
    (g := (stage i p n).rangeRestrict) (stageEquiv i p hF n).bijective]
  have hσ : (iterateFrobeniusEquiv L p n).symm.toRingHom.Flat :=
    .of_bijective (RingEquiv.bijective _)
  exact (RingHom.Flat.of_isPerfectClosure i p hF).comp hσ

include i in
/-- If the Frobenius endomorphism of `K` is flat and every `K`-module has projective dimension at
most `d`, then every module over a perfect closure `i : K →+* L` has projective dimension at most
`d + 1`. -/
theorem hasProjectiveDimensionLE_succ (hF : (frobenius K p).Flat) {d : ℕ}
    (h : ∀ N : ModuleCat.{u} K, HasProjectiveDimensionLE N d) (M : ModuleCat.{u} L) :
    HasProjectiveDimensionLE M (d + 1) := by
  have := flat_range_stage i p hF
  refine ModuleCat.hasProjectiveDimensionLT_succ_of_iSup_eq_top (monotone_range_stage i p)
    (iSup_range_stage i p) M fun n ↦ ?_
  -- A module over the `n`-th stage is a `K`-module along `stageEquiv`, with the same projective
  -- dimension.
  let e := stageEquiv i p hF n
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.symm (e : K →+* (stage i p n).range) e.symm
  let N := ModuleCat.of (stage i p n).range M
  have := h ((ModuleCat.restrictScalars (e : K →+* (stage i p n).range)).obj N)
  let e' : (ModuleCat.restrictScalars (e : K →+* (stage i p n).range)).obj N
      ≃ₛₗ[(e : K →+* (stage i p n).range)] N :=
    { (e : K →+* (stage i p n).range).restrictScalarsSemilinearMap N with
      invFun := fun m ↦ m
      left_inv := RingHom.restrictScalarsSemilinearMap_apply _ N
      right_inv := RingHom.restrictScalarsSemilinearMap_apply _ N }
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e e' d

omit [ExpChar K p] in
include i p in
/-- Over a perfect closure of a regular ring of Krull dimension at most `d`, every module has
projective dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_isRegularRing [IsRegularRing K] {d : ℕ}
    (hd : ringKrullDim K ≤ d) (M : ModuleCat.{u} L) : HasProjectiveDimensionLE M (d + 1) := by
  have := i.expChar (IsPRadical.injective_of_isReduced i p) p
  exact hasProjectiveDimensionLE_succ i p (TauCeti.IsRegularRing.flat_frobenius p)
    (TauCeti.IsRegularRing.hasProjectiveDimensionLE hd) M

section Surjective

variable [Fact p.Prime] {R : Type u} [CommRing R]

include i in
/-- If `K` has prime characteristic `p`, flat Frobenius, and global dimension at most `d`, then
every module over a reduced quotient `R` of a perfect closure `i : K →+* L` has projective
dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_surjective_of_isReduced [IsReduced R]
    (hF : (frobenius K p).Flat) {d : ℕ}
    (h : ∀ N : ModuleCat.{u} K, HasProjectiveDimensionLE N d) {φ : L →+* R}
    (hφ : Function.Surjective φ) (M : ModuleCat.{u} R) :
    HasProjectiveDimensionLE M (d + 1) :=
  φ.hasProjectiveDimensionLE_of_surjective_of_isReduced p hφ
    (hasProjectiveDimensionLE_succ i p hF h ((ModuleCat.restrictScalars φ).obj M))

omit [ExpChar K p] in
include i p in
/-- Over any reduced (equivalently, perfect) quotient of a perfect closure of a regular ring of
Krull dimension at most `d` in prime characteristic `p`, every module has projective dimension at
most `d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_surjective_of_isRegularRing [IsRegularRing K]
    [IsReduced R] {d : ℕ} (hd : ringKrullDim K ≤ d) {φ : L →+* R} (hφ : Function.Surjective φ)
    (M : ModuleCat.{u} R) : HasProjectiveDimensionLE M (d + 1) := by
  have := i.expChar (IsPRadical.injective_of_isReduced i p) p
  exact hasProjectiveDimensionLE_succ_of_surjective_of_isReduced i p
    (TauCeti.IsRegularRing.flat_frobenius p) (TauCeti.IsRegularRing.hasProjectiveDimensionLE hd)
    hφ M

omit [ExpChar K p] in
include i p in
/-- Over any perfect quotient of a perfect closure of a regular ring of Krull dimension at most `d`
in prime characteristic `p`, every module has projective dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_surjective_of_perfectRing [IsRegularRing K]
    [PerfectRing R p] {d : ℕ} (hd : ringKrullDim K ≤ d) {φ : L →+* R}
    (hφ : Function.Surjective φ) (M : ModuleCat.{u} R) :
    HasProjectiveDimensionLE M (d + 1) := by
  have := TauCeti.isReduced_of_perfectRing R p
  exact hasProjectiveDimensionLE_succ_of_surjective_of_isRegularRing i p hd hφ M

end Surjective

end IsPerfectClosure

namespace IsPRadical

variable {K L R : Type u} [CommRing K] [CommRing L] [CommRing R] (i : K →+* L) (p : ℕ)
  [Fact p.Prime] [CharP L p] [IsPRadical i p]

include i in
/-- **Bhatt–Scholze, Proposition 11.31.** Let `K` be a regular ring of Krull dimension at most `d`,
let `i : K →+* L` be a `p`-radical homomorphism into a ring `L` of prime characteristic `p` (for
example a perfect closure of `K`, or `RingHom.id K`), let `σ` be a finite type, and let
`φ : PerfectClosure (MvPolynomial σ L) p →+* R` be a surjection onto a reduced (equivalently,
perfect) ring `R`. Then every `R`-module has projective dimension at most `d + Nat.card σ + 1`. -/
theorem hasProjectiveDimensionLE_perfectClosure_mvPolynomial_of_surjective [IsRegularRing K]
    [IsReduced R] {σ : Type u} [Finite σ] {d : ℕ} (hd : ringKrullDim K ≤ d)
    {φ : PerfectClosure (MvPolynomial σ L) p →+* R} (hφ : Function.Surjective φ)
    (M : ModuleCat.{u} R) : HasProjectiveDimensionLE M (d + Nat.card σ + 1) := by
  have : ExpChar L p := .prime Fact.out
  have := i.expChar (IsPRadical.injective_of_isReduced i p) p
  let j : MvPolynomial σ K →+* PerfectClosure (MvPolynomial σ L) p :=
    (PerfectClosure.of (MvPolynomial σ L) p).comp (MvPolynomial.map i)
  have : IsPRadical (MvPolynomial.map (σ := σ) i) p := MvPolynomial.isPRadical_map i p
  have : IsPRadical (PerfectClosure.of (MvPolynomial σ L) p) p :=
    PerfectClosure.isPRadical (MvPolynomial σ L) p
  have : IsPerfectClosure j p := IsPRadical.trans (MvPolynomial.map i) _ p
  have hd' : ringKrullDim (MvPolynomial σ K) ≤ (d + Nat.card σ : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, Nat.cast_add]
    exact add_le_add_left hd _
  exact IsPerfectClosure.hasProjectiveDimensionLE_succ_of_surjective_of_isRegularRing j p hd' hφ M

end IsPRadical
