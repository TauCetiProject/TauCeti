/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.FieldTheory.PerfectClosure
import TauCeti.Algebra.Category.ModuleCat.Projective.BaseChange
import TauCeti.Algebra.Category.ModuleCat.Projective.SequentialColimit
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.RingTheory.Perfect.PerfectClosure
import TauCeti.RingTheory.Perfect.Tor
import TauCeti.RingTheory.RegularLocalRing.Frobenius

/-!
# Projective dimension over perfections and their perfect quotients

Let `K` be a ring of exponential characteristic `p` whose Frobenius endomorphism is flat, and
suppose that every `K`-module has projective dimension at most `d`. Then every module over a
perfect closure `i : K →+* L`, for instance Mathlib's colimit perfection `PerfectClosure K p`, has
projective dimension at most `d + 1` (`IsPerfectClosure.hasProjectiveDimensionLE_succ`). By Kunz's
theorem this applies to a regular ring `K` of Krull dimension at most `d`, whose Frobenius is flat
and whose modules have projective dimension at most `d`: the perfection of a regular ring of finite
Krull dimension has finite global dimension
(`IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing`).

The perfect closure `L` is the union of the increasing sequence of subrings `i(K) ^ (1 / p ^ n)`,
the images of `x ↦ i(x) ^ (1 / p ^ n)`. Each of them is isomorphic to `K` because `i` is
injective: its kernel is the `p`-nilradical of `K`, which vanishes because flat Frobenius is
injective. The perfect closure is flat over each of them because it is flat over `K`
(`RingHom.Flat.of_isPerfectClosure`). Every module over `L` is then the colimit of its base
changes from these subrings, which have projective dimension at most `d`, and the telescope
sequence adds one (`ModuleCat.hasProjectiveDimensionLT_succ_of_iSup_eq_top`).

In prime characteristic `p`, any surjection `f : P →+* R` between perfect rings is a homological
epimorphism: `Tor_{k+1}^P(R, R) = 0` for all `k` (`TauCeti.isZero_Tor_succ_of_perfectRing`). By
`ModuleCat.hasProjectiveDimensionLT_of_surjective_of_isZero_Tor_succ`, projective dimension does
not increase along `f`: `pd_R M ≤ pd_P M` for every `R`-module `M`
(`TauCeti.projectiveDimension_le_restrictScalars_of_surjective_of_perfectRing`). Combining this
with the bound over a perfect closure yields Proposition 11.31 of Bhatt and Scholze: any perfect
quotient of a `p`-radical extension (in particular, a perfect closure) of a regular ring of Krull
dimension at most `d` has global dimension at most `d + 1`
(`IsPRadical.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective`).

## Main results

* `TauCeti.hasProjectiveDimensionLT_of_surjective_of_perfectRing`: along a surjection `P →+* R`
  of perfect rings of prime characteristic `p`, `pd_P M < n` implies `pd_R M < n`.
* `TauCeti.projectiveDimension_le_restrictScalars_of_surjective_of_perfectRing`: along a
  surjection `P →+* R` of perfect rings of prime characteristic `p`, `pd_R M ≤ pd_P M`.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ`: if Frobenius of `K` is flat and every
  `K`-module has projective dimension at most `d`, then every module over a perfect closure of
  `K` has projective dimension at most `d + 1`.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing`: over a perfect closure of a
  regular ring of Krull dimension at most `d`, every module has projective dimension at most
  `d + 1`.
* `IsPRadical.hasProjectiveDimensionLE_succ_of_surjective`: the bound `d + 1` passes to any
  perfect quotient of a `p`-radical extension of `K` in prime characteristic `p`.
* `IsPRadical.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective`: **Bhatt and
  Scholze, Proposition 11.31**: over any perfect quotient of a `p`-radical extension (in
  particular, a perfect closure) of a regular ring of prime characteristic `p` and Krull dimension
  at most `d`, every module has projective dimension at most `d + 1`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Proposition 11.31.
* E. Kunz, *Characterizations of regular local rings of characteristic p*, Amer. J. Math. 91
  (1969), 772–784.
-/

public section

open CategoryTheory

universe u

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

include i p in
/-- Over a perfect closure of a regular ring of Krull dimension at most `d`, every module has
projective dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_isRegularRing [IsRegularRing K] {d : ℕ}
    (hd : ringKrullDim K ≤ d) (M : ModuleCat.{u} L) : HasProjectiveDimensionLE M (d + 1) :=
  hasProjectiveDimensionLE_succ i p (TauCeti.IsRegularRing.flat_frobenius p)
    (TauCeti.IsRegularRing.hasProjectiveDimensionLE hd) M

end IsPerfectClosure

namespace TauCeti

/-- **Projective dimension does not increase along a surjection of perfect rings.** If
`f : P →+* R` is a surjective homomorphism of perfect rings of prime characteristic `p`, then
every `R`-module whose restriction to `P` has projective dimension `< n` has projective dimension
`< n` over `R`. -/
theorem hasProjectiveDimensionLT_of_surjective_of_perfectRing {P R : Type u} [CommRing P]
    [CommRing R] (f : P →+* R) (p : ℕ) [Fact p.Prime] [ExpChar P p] [PerfectRing P p]
    [PerfectRing R p] (hf : Function.Surjective f) (M : ModuleCat.{u} R) {n : ℕ}
    (hM : HasProjectiveDimensionLT ((ModuleCat.restrictScalars f).obj M) n) :
    HasProjectiveDimensionLT M n := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton M := Module.subsingleton R M
    have := (ModuleCat.isZero_of_subsingleton M).hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge M 0 n (Nat.zero_le n)
  have hp : p.Prime := Fact.out
  have : CharP P p := (expChar_prime_iff (R := P) hp).1 inferInstance
  have : CharP R p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast f, CharP.cast_eq_zero, map_zero]
  have : ExpChar R p := .prime hp
  algebraize [f]
  exact ModuleCat.hasProjectiveDimensionLT_of_surjective_of_isZero_Tor_succ hf M hM
    fun k _ ↦ TauCeti.isZero_Tor_succ_of_perfectRing (p := p) R R k

/-- **Projective dimension does not increase along a surjection of perfect rings.** For a
surjective homomorphism `f : P →+* R` of perfect rings of prime characteristic `p`,
`pd_R M ≤ pd_P M` for every `R`-module `M`. -/
theorem projectiveDimension_le_restrictScalars_of_surjective_of_perfectRing {P R : Type u}
    [CommRing P] [CommRing R] (f : P →+* R) (p : ℕ) [Fact p.Prime] [ExpChar P p]
    [PerfectRing P p] [PerfectRing R p] (hf : Function.Surjective f) (M : ModuleCat.{u} R) :
    projectiveDimension M ≤ projectiveDimension ((ModuleCat.restrictScalars f).obj M) :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun _ h ↦
    hasProjectiveDimensionLT_of_surjective_of_perfectRing f p hf M h

end TauCeti

namespace IsPRadical

variable {K : Type u} {L : Type*} [CommRing K] [CommSemiring L] (i : K →+* L) (p : ℕ) [ExpChar K p]
  [IsPRadical i p]

include i in
/-- If Frobenius of `K` is flat and every `K`-module has projective dimension at most `d`, then
every module over a perfect quotient `R` of a `p`-radical extension (in particular, a perfect
closure) `i : K →+* L` of `K` in prime characteristic `p` has projective dimension at most
`d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_surjective [Fact p.Prime] (hF : (frobenius K p).Flat)
    {d : ℕ} (h : ∀ N : ModuleCat.{u} K, HasProjectiveDimensionLE N d) {R : Type u} [CommRing R]
    [PerfectRing R p] (f : L →+* R) (hf : Function.Surjective f) (M : ModuleCat.{u} R) :
    HasProjectiveDimensionLE M (d + 1) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton M := Module.subsingleton R M
    have := (ModuleCat.isZero_of_subsingleton M).hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge M 0 (d + 2) (Nat.zero_le _)
  have hp : p.Prime := Fact.out
  have : CharP K p := (expChar_prime_iff (R := K) hp).1 inferInstance
  have : CharP R p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast (f.comp i), CharP.cast_eq_zero, map_zero]
  have : ExpChar R p := .prime hp
  let g := PerfectRing.lift (PerfectClosure.of K p) (f.comp i) p
  have hg : Function.Surjective g := (PerfectRing.lift_surjective_iff ..).2 fun z ↦ by
    obtain ⟨w, rfl⟩ := hf z
    obtain ⟨n, y, hy⟩ := IsPRadical.pow_mem i p w
    exact ⟨n, y, by rw [RingHom.comp_apply, hy, map_pow]⟩
  exact TauCeti.hasProjectiveDimensionLT_of_surjective_of_perfectRing g p hg M
    (IsPerfectClosure.hasProjectiveDimensionLE_succ (PerfectClosure.of K p) p hF h _)

include i p in
/-- **Bhatt and Scholze, Proposition 11.31.** Over any perfect quotient `R` of a `p`-radical
extension (in particular, a perfect closure) `i : K →+* L` of a regular ring `K` of prime
characteristic `p` and Krull dimension at most `d`, every module has projective dimension at most
`d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective [Fact p.Prime]
    [IsRegularRing K] {d : ℕ} (hd : ringKrullDim K ≤ d) {R : Type u} [CommRing R]
    [PerfectRing R p] (f : L →+* R) (hf : Function.Surjective f) (M : ModuleCat.{u} R) :
    HasProjectiveDimensionLE M (d + 1) :=
  hasProjectiveDimensionLE_succ_of_surjective i p (TauCeti.IsRegularRing.flat_frobenius p)
    (TauCeti.IsRegularRing.hasProjectiveDimensionLE hd) f hf M

end IsPRadical
