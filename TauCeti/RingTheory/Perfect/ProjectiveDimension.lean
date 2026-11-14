/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension

import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import TauCeti.Algebra.Category.ModuleCat.Monoidal.ProjectiveDimension
import TauCeti.Algebra.Category.ModuleCat.Projective.SequentialColimit
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.RingTheory.Perfect.Basic
import TauCeti.RingTheory.Perfect.PerfectClosure
import TauCeti.RingTheory.Perfect.Tor
import TauCeti.RingTheory.RegularLocalRing.Frobenius

/-!
# Projective dimension over perfect closures and perfect quotients

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

Because higher `Tor` groups of perfect algebras over a perfect ring of prime characteristic `p`
vanish (`TauCeti.isZero_Tor_succ_of_perfectRing`), any ring homomorphism `f : A →+* B` between
perfect rings whose restriction of scalars is full, such as a surjection onto a radical quotient or
a localization, is a homological epimorphism: `pd_B M ≤ pd_A M` for every `B`-module `M`
(`TauCeti.hasProjectiveDimensionLE_of_restrictScalars_of_perfectRing`,
`TauCeti.projectiveDimension_le_restrictScalars_of_perfectRing`). Composing with a surjective
presentation `L →+* R` from a perfect closure of a regular ring of Krull dimension at most `d` onto
a perfect ring `R` bounds the projective dimension of every `R`-module by `d + 1`
(`IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective`), and for a
radical quotient of `PerfectClosure (MvPolynomial σ K) p` on a finite variable set `σ` gives the
bound `d + Nat.card σ + 1`
(`TauCeti.hasProjectiveDimensionLE_succ_perfectClosure_mvPolynomial_quotient`).

## Main results

* `IsPerfectClosure.hasProjectiveDimensionLE_succ`: if Frobenius of `K` is flat and every
  `K`-module has projective dimension at most `d`, then every module over a perfect closure of
  `K` has projective dimension at most `d + 1`.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing`: over a perfect closure of a
  regular ring of Krull dimension at most `d`, every module has projective dimension at most
  `d + 1`.
* `TauCeti.hasProjectiveDimensionLT_of_restrictScalars_of_perfectRing`,
  `TauCeti.hasProjectiveDimensionLE_of_restrictScalars_of_perfectRing`,
  `TauCeti.projectiveDimension_le_restrictScalars_of_perfectRing`: projective dimension bounds
  descend from restriction of scalars along homological epimorphisms of perfect rings.
* `IsPerfectClosure.hasProjectiveDimensionLE_succ_of_surjective`,
  `IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective`: every module
  over a perfect quotient of a perfect closure of a regular ring of Krull dimension at most `d` has
  projective dimension at most `d + 1`.
* `TauCeti.hasProjectiveDimensionLE_succ_perfectClosure_mvPolynomial_quotient`: every module over a
  radical quotient of `PerfectClosure (MvPolynomial σ K) p` for regular `K` of Krull dimension at
  most `d` and finite `σ` has projective dimension at most `d + Nat.card σ + 1`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Proposition 11.31 and Remark 11.32.
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

section RestrictScalars

variable {A B : Type u} [CommRing A] [CommRing B] (p : ℕ) [Fact p.Prime] [ExpChar A p]
  [PerfectRing A p] [PerfectRing B p] (f : A →+* B) [(ModuleCat.restrictScalars.{u} f).Full]

include p in
/-- **Projective dimension along a homological epimorphism of perfect rings (`<` form).** Let `A`
be a perfect ring of prime characteristic `p` and `f : A →+* B` a ring homomorphism to a perfect
ring `B` whose restriction of scalars is full, for instance a surjective homomorphism or a
localization. If a `B`-module `M` has projective dimension less than `n` over `A`, then it has
projective dimension less than `n` over `B`. -/
theorem hasProjectiveDimensionLT_of_restrictScalars_of_perfectRing (M : ModuleCat.{u} B) {n : ℕ}
    (h : HasProjectiveDimensionLT ((ModuleCat.restrictScalars f).obj M) n) :
    HasProjectiveDimensionLT M n :=
  ModuleCat.hasProjectiveDimensionLT_of_restrictScalars f M h fun i _ ↦
    isZero_Tor_succ_restrictScalars_of_perfectRing (p := p) f (ModuleCat.of B B) i

include p in
/-- **Projective dimension along a homological epimorphism of perfect rings.** Let `A` be a perfect
ring of prime characteristic `p` and `f : A →+* B` a ring homomorphism to a perfect ring `B` whose
restriction of scalars is full. If a `B`-module `M` has projective dimension at most `d` over `A`,
then it has projective dimension at most `d` over `B`. -/
theorem hasProjectiveDimensionLE_of_restrictScalars_of_perfectRing (M : ModuleCat.{u} B) {d : ℕ}
    (h : HasProjectiveDimensionLE ((ModuleCat.restrictScalars f).obj M) d) :
    HasProjectiveDimensionLE M d :=
  hasProjectiveDimensionLT_of_restrictScalars_of_perfectRing p f M h

include p in
/-- Along a ring homomorphism `f : A →+* B` between perfect rings of prime characteristic `p` whose
restriction of scalars is full, every `B`-module `M` satisfies `pd_B M ≤ pd_A M`. -/
theorem projectiveDimension_le_restrictScalars_of_perfectRing (M : ModuleCat.{u} B) :
    projectiveDimension M ≤ projectiveDimension ((ModuleCat.restrictScalars f).obj M) :=
  ModuleCat.projectiveDimension_le_restrictScalars f M fun i ↦
    isZero_Tor_succ_restrictScalars_of_perfectRing (p := p) f (ModuleCat.of B B) i

end RestrictScalars

end TauCeti

namespace IsPerfectClosure

variable {K L R : Type u} [CommRing K] [CommRing L] [CommRing R] (i : K →+* L) (p : ℕ)
  [Fact p.Prime] [ExpChar K p] [ExpChar L p] [PerfectRing L p] [IsPerfectClosure i p]
  [PerfectRing R p] {f : L →+* R}

include i in
/-- If the Frobenius endomorphism of `K` is flat, every `K`-module has projective dimension at most
`d`, and `f : L →+* R` is a surjective homomorphism from a perfect closure `i : K →+* L` onto a
perfect ring `R`, then every `R`-module has projective dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLE_succ_of_surjective (hF : (frobenius K p).Flat) {d : ℕ}
    (h : ∀ N : ModuleCat.{u} K, HasProjectiveDimensionLE N d) (hf : Function.Surjective f)
    (M : ModuleCat.{u} R) : HasProjectiveDimensionLE M (d + 1) := by
  have := f.full_restrictScalars hf
  exact TauCeti.hasProjectiveDimensionLE_of_restrictScalars_of_perfectRing p f M
    (hasProjectiveDimensionLE_succ i p hF h _)

include i p in
/-- **Finite global dimension of perfect quotients of regular rings.** Let `i : K →+* L` be a
perfect closure of a regular ring `K` of prime characteristic `p` and Krull dimension at most `d`,
and let `f : L →+* R` be a surjective ring homomorphism onto a perfect ring `R`. Then every
`R`-module has projective dimension at most `d + 1` (Bhatt–Scholze, Proposition 11.31 and
Remark 11.32). -/
theorem hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective [IsRegularRing K] {d : ℕ}
    (hd : ringKrullDim K ≤ d) (hf : Function.Surjective f) (M : ModuleCat.{u} R) :
    HasProjectiveDimensionLE M (d + 1) :=
  hasProjectiveDimensionLE_succ_of_surjective i p (TauCeti.IsRegularRing.flat_frobenius p)
    (TauCeti.IsRegularRing.hasProjectiveDimensionLE hd) hf M

end IsPerfectClosure

namespace TauCeti

universe v in
/-- **Finite global dimension of perfectly finitely presented algebras over a regular base.** Let
`K` be a regular ring of prime characteristic `p` and Krull dimension at most `d`, let `σ` be a
finite indexing type, and let `I` be a radical ideal of `PerfectClosure (MvPolynomial σ K) p`. Then
every module over the quotient `PerfectClosure (MvPolynomial σ K) p ⧸ I` has projective dimension
at most `d + Nat.card σ + 1` (Bhatt–Scholze, Proposition 11.31). -/
theorem hasProjectiveDimensionLE_succ_perfectClosure_mvPolynomial_quotient {K : Type u}
    [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] [IsRegularRing K] {d : ℕ}
    (hd : ringKrullDim K ≤ d) {σ : Type v} [Finite σ]
    {I : Ideal (PerfectClosure (MvPolynomial σ K) p)} (hI : I.IsRadical)
    (M : ModuleCat.{max u v} (PerfectClosure (MvPolynomial σ K) p ⧸ I)) :
    HasProjectiveDimensionLE M (d + Nat.card σ + 1) := by
  have := hI.perfectRing_quotient p
  have hdim : ringKrullDim (MvPolynomial σ K) ≤ (d + Nat.card σ : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, Nat.cast_add]
    gcongr
  exact IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective
    (PerfectClosure.of (MvPolynomial σ K) p) p hdim Ideal.Quotient.mk_surjective M

end TauCeti
