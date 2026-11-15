/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import TauCeti.Algebra.Category.ModuleCat.Projective.ChangeOfRings
import TauCeti.Algebra.Category.ModuleCat.Projective.SequentialColimit
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.RingTheory.Perfect.PerfectClosure
import TauCeti.RingTheory.Perfect.Tor
import TauCeti.RingTheory.RegularLocalRing.Frobenius

/-!
# Projective dimension over perfect quotients of regular perfections

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

When `p` is prime and `g : P →+* R` is a surjective homomorphism from a perfect ring `P` of
characteristic `p` onto a perfect ring `R`, the kernel of `g` is radical, so
`Tor_{n+1}^P(R, M) = 0` for every `R`-module `M`
(`TauCeti.isZero_Tor_succ_restrictScalars_of_surjective`). Because `R ⊗[P] M ≅ M`, extension of
scalars transfers projective-dimension bounds from `P` to `R`
(`TauCeti.hasProjectiveDimensionLT_of_surjective_of_perfectRing`). Combining both steps shows that
if `P₀` is a regular ring of prime characteristic `p` and Krull dimension at most `d`, then for
every surjective homomorphism `PerfectClosure P₀ p →+* R` onto a perfect ring `R`, every
`R`-module has projective dimension at most `d + 1`
(`TauCeti.hasProjectiveDimensionLE_succ_of_surjective_perfectClosure`). Prime characteristic is
needed for the quotient step: in exponential characteristic `1`, every ring satisfies
`PerfectRing _ 1`, while `ℚ[x] ↠ ℚ[x] ⧸ (x ^ 2)` has regular source of dimension `1` and infinite
global dimension on the target.

## Main results

* `IsPerfectClosure.hasProjectiveDimensionLE_succ`: if Frobenius of `K` is flat and every
  `K`-module has projective dimension at most `d`, then every module over a perfect closure of
  `K` has projective dimension at most `d + 1`.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing`: over a perfect closure of a
  regular ring of Krull dimension at most `d`, every module has projective dimension at most
  `d + 1`.
* `TauCeti.hasProjectiveDimensionLT_of_surjective_of_perfectRing`: a surjection of perfect rings
  of prime characteristic transfers projective-dimension bounds from the source to the target.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective` and
  `TauCeti.hasProjectiveDimensionLE_succ_of_surjective_perfectClosure`: every module over a
  perfect quotient of a perfect closure of a regular `𝔽_p`-algebra of Krull dimension at most `d`
  has projective dimension at most `d + 1`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Proposition 11.31, its proof, and Remark 11.32.
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

/-- A ring receiving a homomorphism from a ring of prime characteristic `p` and carrying a
`PerfectRing R p` structure is reduced, including in the trivial case `R = 0`. -/
private theorem isReduced_of_hom_of_perfectRing {P R : Type u} [CommRing P] [CommRing R] (p : ℕ)
    [ExpChar P p] [hp : Fact p.Prime] (g : P →+* R) [PerfectRing R p] : IsReduced R := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact ⟨fun _ _ ↦ Subsingleton.elim _ _⟩
  have : CharP P p := (expChar_prime_iff (R := P) hp.out).1 inferInstance
  have : CharP R p := (CharP.charP_iff_prime_eq_zero hp.out).2 <| by
    rw [← map_natCast g, CharP.cast_eq_zero, map_zero]
  have : ExpChar R p := .prime hp.out
  exact isReduced_of_perfectRing R p

/-- **Projective dimension along a surjection of perfect rings.** Let `g : P →+* R` be a
surjective homomorphism from a perfect ring `P` of prime characteristic `p` onto a perfect ring
`R`. Every bound `< n` on the projective dimension of an `R`-module `M` over `P` transfers to `M`
over `R`. -/
theorem hasProjectiveDimensionLT_of_surjective_of_perfectRing {P R : Type u} [CommRing P]
    [CommRing R] (p : ℕ) [ExpChar P p] [PerfectRing P p] [Fact p.Prime] [PerfectRing R p]
    {g : P →+* R} (hg : Function.Surjective g) (M : ModuleCat.{u} R) (n : ℕ)
    [HasProjectiveDimensionLT ((ModuleCat.restrictScalars g).obj M) n] :
    HasProjectiveDimensionLT M n :=
  have := isReduced_of_hom_of_perfectRing p g
  ModuleCat.hasProjectiveDimensionLT_of_surjective_of_isZero_Tor hg M n fun i _ ↦
    isZero_Tor_succ_restrictScalars_of_surjective (p := p) hg M i

/-- Let `g : P →+* R` be a surjective homomorphism from a perfect ring `P` of prime characteristic
`p` onto a perfect ring `R`. If an `R`-module `M` has projective dimension `≤ d` over `P`, then `M`
has projective dimension `≤ d` over `R`. -/
theorem hasProjectiveDimensionLE_of_surjective_of_perfectRing {P R : Type u} [CommRing P]
    [CommRing R] (p : ℕ) [ExpChar P p] [PerfectRing P p] [Fact p.Prime] [PerfectRing R p]
    {g : P →+* R} (hg : Function.Surjective g) (M : ModuleCat.{u} R) (d : ℕ)
    [HasProjectiveDimensionLE ((ModuleCat.restrictScalars g).obj M) d] :
    HasProjectiveDimensionLE M d :=
  hasProjectiveDimensionLT_of_surjective_of_perfectRing p hg M (d + 1)

/-- Along a surjective homomorphism `g : P →+* R` of perfect rings of prime characteristic `p`,
the projective dimension of any `R`-module `M` over `R` is at most its projective dimension over
`P`. -/
theorem projectiveDimension_le_restrictScalars_of_surjective_of_perfectRing {P R : Type u}
    [CommRing P] [CommRing R] (p : ℕ) [ExpChar P p] [PerfectRing P p] [Fact p.Prime]
    [PerfectRing R p] {g : P →+* R} (hg : Function.Surjective g) (M : ModuleCat.{u} R) :
    projectiveDimension M ≤ projectiveDimension ((ModuleCat.restrictScalars g).obj M) :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun n _ ↦
    hasProjectiveDimensionLT_of_surjective_of_perfectRing p hg M n

end TauCeti

namespace IsPerfectClosure

variable {K L R : Type u} [CommRing K] [CommRing L] [CommRing R] (i : K →+* L) (p : ℕ)
  [ExpChar K p] [ExpChar L p] [PerfectRing L p] [IsPerfectClosure i p] [Fact p.Prime]
  [PerfectRing R p]

include i in
/-- If the Frobenius endomorphism of `K` is flat and every `K`-module has projective dimension at
most `d`, then for every surjective homomorphism `g : L →+* R` from a perfect closure of `K` onto
a perfect ring `R`, every `R`-module has projective dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_surjective (hF : (frobenius K p).Flat) {d : ℕ}
    (h : ∀ N : ModuleCat.{u} K, HasProjectiveDimensionLE N d) {g : L →+* R}
    (hg : Function.Surjective g) (M : ModuleCat.{u} R) :
    HasProjectiveDimensionLE M (d + 1) := by
  have := hasProjectiveDimensionLE_succ i p hF h ((ModuleCat.restrictScalars g).obj M)
  exact TauCeti.hasProjectiveDimensionLE_of_surjective_of_perfectRing p hg M (d + 1)

include i p in
/-- Over a perfect quotient `R` of a perfect closure of a regular ring `K` of prime characteristic
`p` and Krull dimension at most `d`, every `R`-module has projective dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective [IsRegularRing K] {d : ℕ}
    (hd : ringKrullDim K ≤ d) {g : L →+* R} (hg : Function.Surjective g) (M : ModuleCat.{u} R) :
    HasProjectiveDimensionLE M (d + 1) :=
  hasProjectiveDimensionLE_succ_of_surjective i p (TauCeti.IsRegularRing.flat_frobenius p)
    (TauCeti.IsRegularRing.hasProjectiveDimensionLE hd) hg M

end IsPerfectClosure

namespace TauCeti

/-- **Finite global dimension of perfect quotients of regular perfections** (Bhatt–Scholze,
Proposition 11.31). Let `P₀` be a regular ring of prime characteristic `p` and Krull dimension at
most `d`, and let `R` be a perfect ring equipped with a surjective homomorphism
`PerfectClosure P₀ p →+* R`. Then every `R`-module has projective dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_surjective_perfectClosure {P₀ R : Type u} [CommRing P₀]
    [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP P₀ p] [PerfectRing R p] [IsRegularRing P₀]
    {d : ℕ} (hd : ringKrullDim P₀ ≤ d) [Algebra (PerfectClosure P₀ p) R]
    (hsurj : Function.Surjective (algebraMap (PerfectClosure P₀ p) R)) (M : ModuleCat.{u} R) :
    HasProjectiveDimensionLE M (d + 1) := by
  have : ExpChar P₀ p := .prime hp.out
  have : ExpChar (PerfectClosure P₀ p) p := .prime hp.out
  have : IsPerfectClosure (PerfectClosure.of P₀ p) p := PerfectClosure.isPRadical P₀ p
  exact IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective
    (PerfectClosure.of P₀ p) p hd hsurj M

/-- For a surjective homomorphism `PerfectClosure P₀ p →+* R` from the perfection of a regular
`𝔽_p`-algebra `P₀` onto a perfect ring `R`, the projective dimension of every `R`-module is at
most `ringKrullDim P₀ + 1`. -/
theorem projectiveDimension_le_ringKrullDim_add_one_of_surjective_perfectClosure {P₀ R : Type u}
    [CommRing P₀] [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP P₀ p] [PerfectRing R p]
    [IsRegularRing P₀] [Algebra (PerfectClosure P₀ p) R]
    (hsurj : Function.Surjective (algebraMap (PerfectClosure P₀ p) R)) (M : ModuleCat.{u} R) :
    projectiveDimension M ≤ ringKrullDim P₀ + 1 := by
  have := CharP.nontrivial_of_char_ne_one (R := P₀) hp.out.ne_one
  induction h : ringKrullDim P₀ with
  | bot => exact absurd (ringKrullDim_eq_bot_iff_subsingleton.mp h) (not_subsingleton P₀)
  | coe d =>
    induction d with
    | top => exact le_top
    | coe n =>
      exact (projectiveDimension_le_iff M (n + 1)).mpr
        (hasProjectiveDimensionLE_succ_of_surjective_perfectClosure p (h ▸ le_rfl) hsurj M)

end TauCeti
