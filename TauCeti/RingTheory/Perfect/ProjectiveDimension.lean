/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import Mathlib.LinearAlgebra.TensorProduct.Associator
import TauCeti.Algebra.Category.ModuleCat.Projective.SequentialColimit
import TauCeti.Algebra.Category.ModuleCat.Projective.Tor
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.RingTheory.Perfect.PerfectClosure
import TauCeti.RingTheory.Perfect.Tor
import TauCeti.RingTheory.RegularLocalRing.Frobenius

/-!
# Projective dimension over perfect quotients of perfections

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

When `p` is prime, Tor independence of perfect rings (`TauCeti.isZero_Tor_succ_of_perfectRing`)
makes every surjective homomorphism `f : P →+* R` of perfect rings a homological epimorphism:
`Tor_{k+1}^P(R, R) = 0` for all `k` and `R ⊗[P] R ≃ R`. Consequently projective dimension does not
increase along `f` (`TauCeti.hasProjectiveDimensionLT_of_surjective_of_perfectRing`), and the
global dimension bound `d + 1` passes from a perfect closure of `K` to every perfect quotient `R`
(`IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective`).

## Main results

* `TauCeti.hasProjectiveDimensionLT_of_surjective_of_perfectRing`: along a surjective homomorphism
  `f : P →+* R` of perfect rings of prime characteristic `p`, `pd_P M < n` implies `pd_R M < n`.
* `TauCeti.projectiveDimension_le_restrictScalars_of_surjective_of_perfectRing`: the corresponding
  inequality `pd_R M ≤ pd_P M`.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ`: if Frobenius of `K` is flat and every
  `K`-module has projective dimension at most `d`, then every module over a perfect closure of
  `K` has projective dimension at most `d + 1`.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing`: over a perfect closure of a
  regular ring of Krull dimension at most `d`, every module has projective dimension at most
  `d + 1`.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ_of_surjective`: the bound `d + 1` passes to
  every perfect quotient of a perfect closure of `K`.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective`: over a perfect
  quotient of a perfect closure of a regular ring of Krull dimension at most `d`, every module has
  projective dimension at most `d + 1`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Proposition 11.31 and its proof.
* E. Kunz, *Characterizations of regular local rings of characteristic p*, Amer. J. Math. 91
  (1969), 772–784.
-/

public section

open CategoryTheory

universe u

namespace TauCeti

/-- **Projective dimension does not increase along a surjection of perfect rings.** By Tor
independence of perfect rings, a surjective homomorphism `f : P →+* R` of perfect rings of prime
characteristic `p` is a homological epimorphism, so every `R`-module of projective dimension `< n`
over `P` also has projective dimension `< n` over `R`. -/
theorem hasProjectiveDimensionLT_of_surjective_of_perfectRing
    {P R : Type u} [CommRing P] [CommRing R] (p : ℕ) [Fact p.Prime]
    [ExpChar P p] [PerfectRing P p] [ExpChar R p] [PerfectRing R p]
    {f : P →+* R} (hf : Function.Surjective f) (M : ModuleCat.{u} R) {n : ℕ}
    (h : HasProjectiveDimensionLT ((ModuleCat.restrictScalars f).obj M) n) :
    HasProjectiveDimensionLT M n := by
  let := f.toAlgebra
  have : TensorProduct.CompatibleSMul P R R R := .of_algebraMap_surjective R R hf
  exact ModuleCat.hasProjectiveDimensionLT_of_restrictScalars_of_isZero_Tor
    (isZero_Tor_succ_of_perfectRing (A := P) (p := p) R R) M h

/-- **Projective dimension does not increase along a surjection of perfect rings**:
`pd_R M ≤ pd_P M` for every surjective homomorphism `f : P →+* R` of perfect rings of prime
characteristic `p` and every `R`-module `M`. -/
theorem projectiveDimension_le_restrictScalars_of_surjective_of_perfectRing
    {P R : Type u} [CommRing P] [CommRing R] (p : ℕ) [Fact p.Prime]
    [ExpChar P p] [PerfectRing P p] [ExpChar R p] [PerfectRing R p]
    {f : P →+* R} (hf : Function.Surjective f) (M : ModuleCat.{u} R) :
    projectiveDimension M ≤ projectiveDimension ((ModuleCat.restrictScalars f).obj M) :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun _ h ↦
    hasProjectiveDimensionLT_of_surjective_of_perfectRing p hf M h

end TauCeti

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

include i in
/-- Over a perfect quotient of a perfect closure of a ring with flat Frobenius and global dimension
at most `d`, every module has projective dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_surjective [Fact p.Prime] (hF : (frobenius K p).Flat)
    {d : ℕ} (h : ∀ N : ModuleCat.{u} K, HasProjectiveDimensionLE N d)
    {R : Type u} [CommRing R] [ExpChar R p] [PerfectRing R p]
    {f : L →+* R} (hf : Function.Surjective f) (M : ModuleCat.{u} R) :
    HasProjectiveDimensionLE M (d + 1) :=
  TauCeti.hasProjectiveDimensionLT_of_surjective_of_perfectRing p hf M
    (hasProjectiveDimensionLE_succ i p hF h ((ModuleCat.restrictScalars f).obj M))

include i p in
/-- **Global dimension bound for perfect quotients of perfections of regular rings**
(Bhatt–Scholze, Proposition 11.31). If `K` is a regular ring of Krull dimension at most `d` and
`f : L →+* R` is a surjective homomorphism from a perfect closure of `K` onto a perfect ring `R`,
then every `R`-module has projective dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective [Fact p.Prime]
    [IsRegularRing K] {d : ℕ} (hd : ringKrullDim K ≤ d)
    {R : Type u} [CommRing R] [ExpChar R p] [PerfectRing R p]
    {f : L →+* R} (hf : Function.Surjective f) (M : ModuleCat.{u} R) :
    HasProjectiveDimensionLE M (d + 1) :=
  hasProjectiveDimensionLE_succ_of_surjective i p (TauCeti.IsRegularRing.flat_frobenius p)
    (TauCeti.IsRegularRing.hasProjectiveDimensionLE hd) hf M

end IsPerfectClosure
