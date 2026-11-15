/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Archimedean.ClassFormation
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.CyclicTwo

/-!
# Local Tate duality and Euler characteristic at archimedean places

For `F = ℝ` or `w.Completion` at an infinite place `w` and `n ≠ 0`, `h2MuToBr` composed with the
Brauer invariant embeds `H²(G_F, μₙ)` into `n`-torsion of `ℚ/ℤ` (`0` if `w` is complex, `2`-torsion
if real) and lifts along `ZMod.toRatAddCircle n` to an injective map `H²(G_F, μₙ) →+ ZMod n`
(`realH2MuToZMod`, `infiniteH2MuToZMod`).

Since `Gal(ℝˢ/ℝ)` has order `2` and conjugation inverts `μₙ` (`smul_kummerCoeff_real_eq_neg`,
`smul_kummerCoeff_completion_eq_neg`), `Cup.Duality.CyclicTwo` yields:
* **Archimedean local Tate duality in degree one:** for finite discrete `A` killed by `n`,
  `dualityMap1` and `realTatePairing` / `infiniteTatePairing` are bijective.
* **Archimedean local Euler characteristic:** for any topological `A` killed by `n`,
  `Nat.card A ^ w.mult * Nat.card (H¹(G_w, A)) = Nat.card A^{G_w} * Nat.card (A')^{G_w}`.

## References

* J. Tate, *Duality theorems in Galois cohomology over number fields*, ICM (1962), 288–295.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Theorem 2.13.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.2.17).
-/

public noncomputable section

open NumberField NumberField.InfinitePlace TauCeti ContCohomology

namespace TauCeti.ClassFieldTheory

section BrInvLift

variable {F : Type*} [Field F] [CharZero F] (n : ℕ) [NeZero n]

private theorem nsmul_brInv_h2MuToBr_eq_zero (inv : Br F →+ AddCircle (1 : ℚ))
    (x : continuousCohomology 2 (muNRep n F)) : n • inv (h2MuToBr n F x) = 0 := by
  rw [← map_nsmul,
    (h2MuToBr_range n F (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit _).mp ⟨x, rfl⟩, map_zero]

private def h2MuToZModFun (inv : Br F →+ AddCircle (1 : ℚ))
    (x : continuousCohomology 2 (muNRep n F)) : ZMod n :=
  (ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero n (nsmul_brInv_h2MuToBr_eq_zero n inv x)).choose

private theorem toRatAddCircle_h2MuToZModFun (inv : Br F →+ AddCircle (1 : ℚ))
    (x : continuousCohomology 2 (muNRep n F)) :
    ZMod.toRatAddCircle n (h2MuToZModFun n inv x) = inv (h2MuToBr n F x) :=
  (ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero n
    (nsmul_brInv_h2MuToBr_eq_zero n inv x)).choose_spec

private def h2MuToZModOfBrInv (inv : Br F →+ AddCircle (1 : ℚ)) :
    continuousCohomology 2 (muNRep n F) →+ ZMod n where
  toFun := h2MuToZModFun n inv
  map_zero' := ZMod.toRatAddCircle_injective n (by simp [toRatAddCircle_h2MuToZModFun])
  map_add' _ _ := ZMod.toRatAddCircle_injective n (by simp [toRatAddCircle_h2MuToZModFun])

private theorem toRatAddCircle_h2MuToZModOfBrInv (inv : Br F →+ AddCircle (1 : ℚ))
    (x : continuousCohomology 2 (muNRep n F)) :
    ZMod.toRatAddCircle n (h2MuToZModOfBrInv n inv x) = inv (h2MuToBr n F x) :=
  toRatAddCircle_h2MuToZModFun n inv x

private theorem h2MuToZModOfBrInv_injective {inv : Br F →+ AddCircle (1 : ℚ)}
    (hinv : Function.Injective inv) : Function.Injective (h2MuToZModOfBrInv n inv) := fun x y hxy =>
  h2MuToBr_injective n F (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit <| hinv <| by
    rw [← toRatAddCircle_h2MuToZModOfBrInv n inv x, ← toRatAddCircle_h2MuToZModOfBrInv n inv y, hxy]

private theorem two_nsmul_h2MuToZModOfBrInv {inv : Br F →+ AddCircle (1 : ℚ)}
    (h2 : inv.range ≤ AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (2 : ℤ))
    (x : continuousCohomology 2 (muNRep n F)) : 2 • h2MuToZModOfBrInv n inv x = 0 :=
  ZMod.toRatAddCircle_injective n <| by
    rw [map_nsmul, toRatAddCircle_h2MuToZModOfBrInv,
      AddSubgroup.torsionBy.nsmul_iff.mp (h2 ⟨_, rfl⟩), map_zero]

end BrInvLift

section RealInvariant

variable (n : ℕ) [NeZero n]

/-- **The normalized real invariant on `H²(G_ℝ, μₙ)`**, valued in `ZMod n`. -/
def realH2MuToZMod : continuousCohomology 2 (muNRep n ℝ) →+ ZMod n :=
  h2MuToZModOfBrInv n realInv

/-- Embedding `realH2MuToZMod` into `ℚ/ℤ` recovers the real Brauer invariant. -/
@[simp]
theorem toRatAddCircle_realH2MuToZMod (x : continuousCohomology 2 (muNRep n ℝ)) :
    ZMod.toRatAddCircle n (realH2MuToZMod n x) = realInv (h2MuToBr n ℝ x) :=
  toRatAddCircle_h2MuToZModOfBrInv n realInv x

/-- `realH2MuToZMod n x = z` iff the real Brauer invariant of `x` is the image of `z` in `ℚ/ℤ`. -/
theorem realH2MuToZMod_eq_iff (x : continuousCohomology 2 (muNRep n ℝ)) (z : ZMod n) :
    realH2MuToZMod n x = z ↔ realInv (h2MuToBr n ℝ x) = ZMod.toRatAddCircle n z := by
  rw [← (ZMod.toRatAddCircle_injective n).eq_iff, toRatAddCircle_realH2MuToZMod]

/-- **The real roots-of-unity invariant into `ZMod n` is injective** for every nonzero `n`. -/
theorem realH2MuToZMod_injective : Function.Injective (realH2MuToZMod n) :=
  h2MuToZModOfBrInv_injective n realInv_injective

/-- Every value of `realH2MuToZMod` is `2`-torsion in `ZMod n`. -/
theorem two_nsmul_realH2MuToZMod (x : continuousCohomology 2 (muNRep n ℝ)) :
    2 • realH2MuToZMod n x = 0 :=
  two_nsmul_h2MuToZModOfBrInv n (SetLike.coe_subset_coe.mp range_realInv.le) x

end RealInvariant

section InfiniteInvariant

variable {K : Type*} [Field K] (w : InfinitePlace K) (n : ℕ) [NeZero n]

/-- **The normalized archimedean invariant on `H²(G_{K_w}, μₙ)`**, valued in `ZMod n`. -/
def infiniteH2MuToZMod : continuousCohomology 2 (muNRep n w.Completion) →+ ZMod n :=
  have := (Completion.extensionEmbedding w).charZero
  h2MuToZModOfBrInv n (infiniteInvMap w)

/-- Embedding `infiniteH2MuToZMod` into `ℚ/ℤ` recovers the archimedean Brauer invariant. -/
@[simp]
theorem toRatAddCircle_infiniteH2MuToZMod (x : continuousCohomology 2 (muNRep n w.Completion)) :
    ZMod.toRatAddCircle n (infiniteH2MuToZMod w n x) =
      infiniteInvMap w (h2MuToBr n w.Completion x) :=
  have := (Completion.extensionEmbedding w).charZero
  toRatAddCircle_h2MuToZModOfBrInv n (infiniteInvMap w) x

/-- `infiniteH2MuToZMod w n x = z` iff the archimedean Brauer invariant of `x` maps to `z`. -/
theorem infiniteH2MuToZMod_eq_iff (x : continuousCohomology 2 (muNRep n w.Completion))
    (z : ZMod n) : infiniteH2MuToZMod w n x = z ↔
      infiniteInvMap w (h2MuToBr n w.Completion x) = ZMod.toRatAddCircle n z := by
  rw [← (ZMod.toRatAddCircle_injective n).eq_iff, toRatAddCircle_infiniteH2MuToZMod]

/-- **The archimedean roots-of-unity invariant into `ZMod n` is injective** at every `w`. -/
theorem infiniteH2MuToZMod_injective : Function.Injective (infiniteH2MuToZMod w n) :=
  have := (Completion.extensionEmbedding w).charZero
  h2MuToZModOfBrInv_injective n (infiniteInvMap_injective w)

/-- At a complex place, `infiniteH2MuToZMod` is the zero homomorphism. -/
@[simp]
theorem infiniteH2MuToZMod_of_isComplex (hw : w.IsComplex) : infiniteH2MuToZMod w n = 0 := by
  ext x
  exact ZMod.toRatAddCircle_injective n (by simp [hw])

/-- Every value of `infiniteH2MuToZMod` is `2`-torsion in `ZMod n`. -/
theorem two_nsmul_infiniteH2MuToZMod (x : continuousCohomology 2 (muNRep n w.Completion)) :
    2 • infiniteH2MuToZMod w n x = 0 := by
  have := (Completion.extensionEmbedding w).charZero
  rcases w.isReal_or_isComplex with hw | hw
  · exact two_nsmul_h2MuToZModOfBrInv n
      (SetLike.coe_subset_coe.mp (range_infiniteInvMap_of_isReal w hw).le) x
  · simp [hw]

end InfiniteInvariant

/-- The absolute Galois group `Gal(ℝˢ/ℝ)` has order two. -/
theorem natCard_absoluteGaloisGroup_real : Nat.card (AbsoluteGaloisGroup ℝ) = 2 := by
  rw [Nat.card_congr (Completion.ringEquivRealOfIsReal
      Rat.isReal_infinitePlace).absoluteGaloisGroupCongr.toEquiv,
    natCard_absoluteGaloisGroup_of_isReal Rat.infinitePlace Rat.isReal_infinitePlace]

/-- `Gal(ℝˢ/ℝ)` is finite (of order two). -/
instance finite_absoluteGaloisGroup_real : Finite (AbsoluteGaloisGroup ℝ) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_absoluteGaloisGroup_real]; decide)

/-- The Krull topology on `Gal(ℝˢ/ℝ)` is discrete. -/
theorem discreteTopology_absoluteGaloisGroup_real : DiscreteTopology (AbsoluteGaloisGroup ℝ) :=
  have : T2Space (AbsoluteGaloisGroup ℝ) := krullTopology_t2
  Finite.instDiscreteTopology

/-- The Krull topology on `Gal(K_wˢ/K_w)` at an infinite place `w` is discrete. -/
theorem discreteTopology_absoluteGaloisGroup_completion {K : Type*} [Field K]
    (w : InfinitePlace K) : DiscreteTopology (AbsoluteGaloisGroup w.Completion) := by
  have : T2Space (AbsoluteGaloisGroup w.Completion) := krullTopology_t2
  have : Finite (AbsoluteGaloisGroup w.Completion) := w.isReal_or_isComplex.elim
    (fun hw => Nat.finite_of_card_ne_zero (by
      rw [natCard_absoluteGaloisGroup_of_isReal w hw]; decide))
    fun hw => @Finite.of_subsingleton _
      (Completion.ringEquivComplexOfIsComplex hw).absoluteGaloisGroupCongr.symm.toEquiv.subsingleton
  exact Finite.instDiscreteTopology

private theorem smul_kummerCoeff_eq_neg_iff {F : Type*} [Field F] {n : ℕ}
    (g : AbsoluteGaloisGroup F) (y : KummerCoeff F n) :
    g • y = -y ↔
      g (((y.toMul : rootsOfUnity n (SeparableClosure F)) : (SeparableClosure F)ˣ) :
        SeparableClosure F) =
      (((y.toMul : rootsOfUnity n (SeparableClosure F)) : (SeparableClosure F)ˣ) :
        SeparableClosure F)⁻¹ := by
  rw [← Additive.toMul.injective.eq_iff, Subtype.ext_iff, Units.ext_iff]
  simp [AlgEquiv.smul_units_def]

private theorem smul_kummerCoeff_congr_eq_neg {F L : Type*} [Field F] [Field L] (e : F ≃+* L)
    {n : ℕ} (hF : ∀ g : AbsoluteGaloisGroup F, g ≠ 1 → ∀ y : KummerCoeff F n, g • y = -y)
    {g : AbsoluteGaloisGroup L} (hg : g ≠ 1) (y : KummerCoeff L n) : g • y = -y := by
  have hg' : e.absoluteGaloisGroupCongr g ≠ 1 := fun h =>
    hg (e.absoluteGaloisGroupCongr.injective (h.trans (map_one _).symm))
  let u : (SeparableClosure L)ˣ := (y.toMul : rootsOfUnity n (SeparableClosure L))
  let uF : (SeparableClosure F)ˣ := Units.map e.separableClosureCongr.toRingHom.toMonoidHom u
  have huF : uF ∈ rootsOfUnity n (SeparableClosure F) :=
    (mem_rootsOfUnity n uF).mpr (by rw [← map_pow, (mem_rootsOfUnity n u).mp y.toMul.2, map_one])
  have hval := (smul_kummerCoeff_eq_neg_iff (e.absoluteGaloisGroupCongr g)
    (Additive.ofMul ⟨uF, huF⟩)).mp (hF _ hg' (Additive.ofMul ⟨uF, huF⟩))
  rw [smul_kummerCoeff_eq_neg_iff]
  refine e.separableClosureCongr.injective ?_
  rw [map_inv₀]
  simpa [u, uF, RingEquiv.absoluteGaloisGroupCongr_apply] using hval

/-- **Complex conjugation inverts every root of unity** in `KummerCoeff ℝ n`. -/
theorem smul_kummerCoeff_real_eq_neg {n : ℕ} [NeZero n] {g : AbsoluteGaloisGroup ℝ} (hg : g ≠ 1)
    (y : KummerCoeff ℝ n) : g • y = -y := by
  refine smul_kummerCoeff_congr_eq_neg
    (Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) (fun τ hτ z => ?_) hg y
  set σ : Gal(AlgebraicClosure Rat.infinitePlace.Completion / Rat.infinitePlace.Completion) :=
    (absoluteGaloisGroupRestrictEquiv Rat.infinitePlace.Completion).symm τ
  have hσ : σ ≠ 1 := fun h => hτ <|
    (absoluteGaloisGroupRestrictEquiv Rat.infinitePlace.Completion).symm.injective
      (h.trans (map_one _).symm)
  let u : (SeparableClosure Rat.infinitePlace.Completion)ˣ :=
    (z.toMul : rootsOfUnity n (SeparableClosure Rat.infinitePlace.Completion))
  have hz : ((u : SeparableClosure Rat.infinitePlace.Completion) :
      AlgebraicClosure Rat.infinitePlace.Completion) ^ n = 1 := by
    have hu : (u : SeparableClosure Rat.infinitePlace.Completion) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity n u).mp z.toMul.2, Units.val_one]
    exact_mod_cast hu
  have hinv := fieldAbsoluteGaloisGroup_apply_eq_inv Rat.infinitePlace hσ (NeZero.ne n) hz
  rw [absoluteGaloisGroupRestrictEquiv_symm_apply_coe] at hinv
  exact (smul_kummerCoeff_eq_neg_iff _ _).mpr (Subtype.ext hinv)

/-- **At an infinite place, any nontrivial element of `Gal(K_wˢ/K_w)` inverts every root of
unity.** -/
theorem smul_kummerCoeff_completion_eq_neg {K : Type*} [Field K] (w : InfinitePlace K)
    {n : ℕ} [NeZero n] {g : AbsoluteGaloisGroup w.Completion} (hg : g ≠ 1)
    (y : KummerCoeff w.Completion n) : g • y = -y := by
  rcases w.isReal_or_isComplex with hw | hw
  · exact smul_kummerCoeff_congr_eq_neg (Completion.ringEquivRealOfIsReal hw).symm
      (fun _ h => smul_kummerCoeff_real_eq_neg h) hg y
  · have :=
      (Completion.ringEquivComplexOfIsComplex hw).absoluteGaloisGroupCongr.symm.toEquiv.subsingleton
    exact absurd (Subsingleton.elim g 1) hg

section AbstractFieldDuality

local notation "Gal" => AbsoluteGaloisGroup

variable {F : Type*} [Field F] (A : Type*) [AddCommGroup A] [TopologicalSpace A]
  [DiscreteTopology A] [DistribMulAction (Gal F) A] [ContinuousSMul (Gal F) A] [Finite A]

private def tatePairingOfH2MuHom {n : ℕ} (ι : continuousCohomology 2 (muNRep n F) →+ ZMod n) :
    H1 (Gal F) A →+ H1 (Gal F) (InternalHom (Gal F) A (KummerCoeff F n)) →+ ZMod n :=
  (AddMonoidHom.compHom (ι.comp (muNRepH2Equiv n F).toAddMonoidHom)).comp
    (dualityMap1 (Gal F) A (KummerCoeff F n))

private theorem toRatAddCircle_tatePairingOfH2MuHom {n : ℕ}
    (ι : continuousCohomology 2 (muNRep n F) →+ ZMod n) (inv : Br F →+ AddCircle (1 : ℚ))
    (hι : ∀ z, ZMod.toRatAddCircle n (ι z) = inv (h2MuToBr n F z)) (x : H1 (Gal F) A)
    (y : H1 (Gal F) (InternalHom (Gal F) A (KummerCoeff F n))) :
    ZMod.toRatAddCircle n (tatePairingOfH2MuHom A ι x y) =
      inv (h2MuToBr n F (muNRepH2Equiv n F (dualityMap1 (Gal F) A (KummerCoeff F n) x y))) :=
  hι _

private theorem tatePairingOfH2MuHom_eq_zero {n : ℕ}
    {ι : continuousCohomology 2 (muNRep n F) →+ ZMod n} (hι : ι = 0) :
    tatePairingOfH2MuHom A ι = 0 := by
  ext x y
  simp [tatePairingOfH2MuHom, hι]

variable {A}

private theorem dualityMap1_kummerCoeff_bijective_of_natCard_eq_two_or_subsingleton
    (hG : Nat.card (Gal F) = 2 ∨ Subsingleton (Gal F)) {n : ℕ} [NeZero n] (hn : IsUnit (n : F))
    (hA : ∀ a : A, n • a = 0) (hneg : ∀ g : Gal F, g ≠ 1 → ∀ y : KummerCoeff F n, g • y = -y) :
    Function.Bijective (dualityMap1 (Gal F) A (KummerCoeff F n)) :=
  hG.elim
    (fun h2 => dualityMap1_bijective_of_natCard_eq_two h2 (kummerCoeffAddEquivZMod hn) hA hneg)
    (fun hsub => dualityMap1_bijective_of_subsingleton hsub)

private theorem tatePairingOfH2MuHom_bijective_of_natCard_eq_two_or_subsingleton
    (hG : Nat.card (Gal F) = 2 ∨ Subsingleton (Gal F)) {n : ℕ} [NeZero n] (hn : IsUnit (n : F))
    {ι : continuousCohomology 2 (muNRep n F) →+ ZMod n} (hι : Function.Injective ι)
    (hA : ∀ a : A, n • a = 0) (hneg : ∀ g : Gal F, g ≠ 1 → ∀ y : KummerCoeff F n, g • y = -y) :
    Function.Bijective (tatePairingOfH2MuHom A ι) :=
  hG.elim
    (fun h2 =>
      bijective_compHom_dualityMap1_of_natCard_eq_two h2 (kummerCoeffAddEquivZMod hn) hA hneg
        (ι := ι.comp (muNRepH2Equiv n F).toAddMonoidHom) (hι.comp (muNRepH2Equiv n F).injective))
    (fun hsub => bijective_compHom_dualityMap1_of_subsingleton hsub _)

end AbstractFieldDuality

section RealDuality

/-- Every class in `H¹(G_ℝ, A)` is `2`-torsion. -/
theorem two_nsmul_H1_real {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DistribMulAction (AbsoluteGaloisGroup ℝ) A]
    [ContinuousSMul (AbsoluteGaloisGroup ℝ) A] (x : H1 (AbsoluteGaloisGroup ℝ) A) : 2 • x = 0 :=
  two_nsmul_H1_eq_zero_of_natCard_eq_two natCard_absoluteGaloisGroup_real x

/-- **Real local Euler characteristic in degree one** (`0 = 0` when `A` is infinite). -/
theorem natCard_mul_natCard_H1_real {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DistribMulAction (AbsoluteGaloisGroup ℝ) A]
    [ContinuousSMul (AbsoluteGaloisGroup ℝ) A] {n : ℕ} [NeZero n] (hA : ∀ a : A, n • a = 0) :
    Nat.card A * Nat.card (H1 (AbsoluteGaloisGroup ℝ) A) =
      Nat.card (H0 (AbsoluteGaloisGroup ℝ) A) *
        Nat.card (H0 (AbsoluteGaloisGroup ℝ)
          (InternalHom (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n))) :=
  have := discreteTopology_absoluteGaloisGroup_real
  natCard_mul_natCard_H1_of_natCard_eq_two natCard_absoluteGaloisGroup_real
    (kummerCoeffAddEquivZMod (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit) hA
    (fun _ hg => smul_kummerCoeff_real_eq_neg hg)

variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction (AbsoluteGaloisGroup ℝ) A] [ContinuousSMul (AbsoluteGaloisGroup ℝ) A]
  [Finite A]

/-- **Tate's degree-one local pairing over `ℝ`**, valued in `ZMod n`. -/
def realTatePairing (n : ℕ) [NeZero n] : H1 (AbsoluteGaloisGroup ℝ) A →+
    H1 (AbsoluteGaloisGroup ℝ) (InternalHom (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n)) →+
      ZMod n :=
  tatePairingOfH2MuHom A (realH2MuToZMod n)

/-- `realTatePairing` evaluates `dualityMap1` and applies `realH2MuToZMod`. -/
@[simp]
theorem realTatePairing_apply (n : ℕ) [NeZero n] (x : H1 (AbsoluteGaloisGroup ℝ) A)
    (y : H1 (AbsoluteGaloisGroup ℝ) (InternalHom (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n))) :
    realTatePairing A n x y = realH2MuToZMod n
      (muNRepH2Equiv n ℝ (dualityMap1 (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n) x y)) :=
  (rfl)

/-- Embedded into `ℚ/ℤ`, `realTatePairing` is the real Brauer invariant of the cup product. -/
theorem toRatAddCircle_realTatePairing (n : ℕ) [NeZero n] (x : H1 (AbsoluteGaloisGroup ℝ) A)
    (y : H1 (AbsoluteGaloisGroup ℝ) (InternalHom (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n))) :
    ZMod.toRatAddCircle n (realTatePairing A n x y) = realInv (h2MuToBr n ℝ
      (muNRepH2Equiv n ℝ (dualityMap1 (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n) x y))) :=
  toRatAddCircle_tatePairingOfH2MuHom A (realH2MuToZMod n) realInv
    (toRatAddCircle_realH2MuToZMod n) x y

variable {A} {n : ℕ} [NeZero n]

/-- Over `ℝ`, `H¹(G_ℝ, A)` and `H¹(G_ℝ, Hom(A, μₙ))` have equal cardinality. -/
theorem natCard_H1_internalHom_kummerCoeff_real (hA : ∀ a : A, n • a = 0) :
    Nat.card (H1 (AbsoluteGaloisGroup ℝ)
      (InternalHom (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n))) =
      Nat.card (H1 (AbsoluteGaloisGroup ℝ) A) :=
  natCard_H1_internalHom_eq_of_natCard_eq_two natCard_absoluteGaloisGroup_real
    (kummerCoeffAddEquivZMod (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit) hA
    (fun _ hg => smul_kummerCoeff_real_eq_neg hg)

/-- **Real local Tate duality in degree one (cohomological target).** -/
theorem dualityMap1_kummerCoeff_real_bijective (hA : ∀ a : A, n • a = 0) :
    Function.Bijective (dualityMap1 (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n)) :=
  dualityMap1_kummerCoeff_bijective_of_natCard_eq_two_or_subsingleton
    (Or.inl natCard_absoluteGaloisGroup_real)
    (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit hA (fun _ hg => smul_kummerCoeff_real_eq_neg hg)

/-- **Real local Tate duality in degree one (`ℤ/n` target).** -/
theorem realTatePairing_bijective (hA : ∀ a : A, n • a = 0) :
    Function.Bijective (realTatePairing A n) :=
  tatePairingOfH2MuHom_bijective_of_natCard_eq_two_or_subsingleton
    (Or.inl natCard_absoluteGaloisGroup_real) (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit
    (realH2MuToZMod_injective n) hA (fun _ hg => smul_kummerCoeff_real_eq_neg hg)

end RealDuality

section InfiniteDuality

variable {K : Type*} [Field K] (w : InfinitePlace K)

private theorem natCard_eq_two_or_subsingleton_completion :
    Nat.card (AbsoluteGaloisGroup w.Completion) = 2 ∨
      Subsingleton (AbsoluteGaloisGroup w.Completion) :=
  w.isReal_or_isComplex.imp (natCard_absoluteGaloisGroup_of_isReal w) fun hw =>
    (Completion.ringEquivComplexOfIsComplex hw).absoluteGaloisGroupCongr.symm.toEquiv.subsingleton

/-- At any infinite place `w`, every class in `H¹(G_{K_w}, A)` is `2`-torsion. -/
theorem two_nsmul_H1_completion {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DistribMulAction (AbsoluteGaloisGroup w.Completion) A]
    [ContinuousSMul (AbsoluteGaloisGroup w.Completion) A]
    (x : H1 (AbsoluteGaloisGroup w.Completion) A) : 2 • x = 0 := by
  rcases natCard_eq_two_or_subsingleton_completion w with h2 | _
  · exact two_nsmul_H1_eq_zero_of_natCard_eq_two h2 x
  · have := subsingleton_H1_of_subsingleton (AbsoluteGaloisGroup w.Completion) A
    exact Subsingleton.elim _ _

/-- **Archimedean local Euler characteristic in degree one** (`0 = 0` when `A` is infinite). -/
theorem natCard_pow_mult_mul_natCard_H1_completion {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DistribMulAction (AbsoluteGaloisGroup w.Completion) A]
    [ContinuousSMul (AbsoluteGaloisGroup w.Completion) A] {n : ℕ} [NeZero n]
    (hA : ∀ a : A, n • a = 0) :
    Nat.card A ^ w.mult * Nat.card (H1 (AbsoluteGaloisGroup w.Completion) A) =
      Nat.card (H0 (AbsoluteGaloisGroup w.Completion) A) *
        Nat.card (H0 (AbsoluteGaloisGroup w.Completion)
          (InternalHom (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n))) := by
  have := (Completion.extensionEmbedding w).charZero
  have hn : IsUnit (n : w.Completion) := (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit
  rcases w.isReal_or_isComplex with hw | hw
  · have := discreteTopology_absoluteGaloisGroup_completion w
    rw [hw.mult_eq_one, pow_one]
    exact natCard_mul_natCard_H1_of_natCard_eq_two (natCard_absoluteGaloisGroup_of_isReal w hw)
      (kummerCoeffAddEquivZMod hn) hA (fun _ hg => smul_kummerCoeff_completion_eq_neg w hg)
  · have :=
      (Completion.ringEquivComplexOfIsComplex hw).absoluteGaloisGroupCongr.symm.toEquiv.subsingleton
    rw [hw.mult_eq_two]
    exact natCard_sq_mul_natCard_H1_of_subsingleton (kummerCoeffAddEquivZMod hn) hA

variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction (AbsoluteGaloisGroup w.Completion) A]
  [ContinuousSMul (AbsoluteGaloisGroup w.Completion) A] [Finite A]

/-- **Tate's degree-one local pairing at an infinite place `w`**, valued in `ZMod n`. -/
def infiniteTatePairing (n : ℕ) [NeZero n] : H1 (AbsoluteGaloisGroup w.Completion) A →+
    H1 (AbsoluteGaloisGroup w.Completion)
      (InternalHom (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n)) →+ ZMod n :=
  tatePairingOfH2MuHom A (infiniteH2MuToZMod w n)

/-- `infiniteTatePairing` evaluates `dualityMap1` and applies `infiniteH2MuToZMod w n`. -/
@[simp]
theorem infiniteTatePairing_apply (n : ℕ) [NeZero n]
    (x : H1 (AbsoluteGaloisGroup w.Completion) A)
    (y : H1 (AbsoluteGaloisGroup w.Completion)
      (InternalHom (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n))) :
    infiniteTatePairing w A n x y = infiniteH2MuToZMod w n (muNRepH2Equiv n w.Completion
      (dualityMap1 (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n) x y)) :=
  (rfl)

/-- In `ℚ/ℤ`, `infiniteTatePairing` is the archimedean Brauer invariant of the cup product. -/
theorem toRatAddCircle_infiniteTatePairing (n : ℕ) [NeZero n]
    (x : H1 (AbsoluteGaloisGroup w.Completion) A)
    (y : H1 (AbsoluteGaloisGroup w.Completion)
      (InternalHom (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n))) :
    ZMod.toRatAddCircle n (infiniteTatePairing w A n x y) = infiniteInvMap w (h2MuToBr n
      w.Completion (muNRepH2Equiv n w.Completion
        (dualityMap1 (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n) x y))) :=
  toRatAddCircle_tatePairingOfH2MuHom A (infiniteH2MuToZMod w n) (infiniteInvMap w)
    (toRatAddCircle_infiniteH2MuToZMod w n) x y

/-- At a complex place, `infiniteTatePairing` is the zero homomorphism. -/
@[simp]
theorem infiniteTatePairing_of_isComplex (hw : w.IsComplex) (n : ℕ) [NeZero n] :
    infiniteTatePairing w A n = 0 :=
  tatePairingOfH2MuHom_eq_zero A (infiniteH2MuToZMod_of_isComplex w n hw)

variable {A} {n : ℕ} [NeZero n]

/-- At any infinite place `w`, `#H¹(G_{K_w}, Hom(A, μₙ)) = #H¹(G_{K_w}, A)`. -/
theorem natCard_H1_internalHom_kummerCoeff_completion (hA : ∀ a : A, n • a = 0) :
    Nat.card (H1 (AbsoluteGaloisGroup w.Completion)
      (InternalHom (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n))) =
      Nat.card (H1 (AbsoluteGaloisGroup w.Completion) A) := by
  have := (Completion.extensionEmbedding w).charZero
  rcases natCard_eq_two_or_subsingleton_completion w with h2 | _
  · exact natCard_H1_internalHom_eq_of_natCard_eq_two h2
      (kummerCoeffAddEquivZMod (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit) hA
      (fun _ hg => smul_kummerCoeff_completion_eq_neg w hg)
  · have h1 := subsingleton_H1_of_subsingleton (AbsoluteGaloisGroup w.Completion) A
    have h2 := subsingleton_H1_of_subsingleton (AbsoluteGaloisGroup w.Completion)
      (InternalHom (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n))
    exact (Nat.card_eq_one_iff_unique.mpr ⟨h2, ⟨0⟩⟩).trans
      (Nat.card_eq_one_iff_unique.mpr ⟨h1, ⟨0⟩⟩).symm

/-- **Archimedean local Tate duality in degree one (cohomological target).** -/
theorem dualityMap1_kummerCoeff_completion_bijective (hA : ∀ a : A, n • a = 0) :
    Function.Bijective
      (dualityMap1 (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n)) := by
  have := (Completion.extensionEmbedding w).charZero
  exact dualityMap1_kummerCoeff_bijective_of_natCard_eq_two_or_subsingleton
    (natCard_eq_two_or_subsingleton_completion w)
    (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit hA
    (fun _ hg => smul_kummerCoeff_completion_eq_neg w hg)

/-- **Archimedean local Tate duality in degree one (`ℤ/n` target).** -/
theorem infiniteTatePairing_bijective (hA : ∀ a : A, n • a = 0) :
    Function.Bijective (infiniteTatePairing w A n) := by
  have := (Completion.extensionEmbedding w).charZero
  exact tatePairingOfH2MuHom_bijective_of_natCard_eq_two_or_subsingleton
    (natCard_eq_two_or_subsingleton_completion w)
    (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit (infiniteH2MuToZMod_injective w n) hA
    (fun _ hg => smul_kummerCoeff_completion_eq_neg w hg)

end InfiniteDuality

end TauCeti.ClassFieldTheory
