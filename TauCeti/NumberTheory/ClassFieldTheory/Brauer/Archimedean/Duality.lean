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

Let `F` be either `ℝ` or the completion `w.Completion` of a field `K` at an infinite place `w`,
and let `n` be a nonzero natural number. Unlike at a nonarchimedean local field, the roots-of-unity
cohomology `H²(G_F, μₙ)` is not isomorphic to `ℤ/n` in general: at a complex place it vanishes, and
over `ℝ` or a real completion it embeds via `h2MuToBr` and the Brauer invariant into the `2`-torsion
of `ℚ/ℤ`, so it has order `gcd(n, 2)`. Nevertheless, every image class in `ℚ/ℤ` is killed by `n`
and therefore lifts uniquely along `ZMod.toRatAddCircle n : ℤ/n →+ ℚ/ℤ` to an injective invariant
homomorphism

```text
H²(G_F, μₙ) →+ ℤ/n
```

(`realH2MuToZMod` over `ℝ` and `infiniteH2MuToZMod w` at an infinite place `w`).

Because `G_ℝ` has order `2` and its nontrivial element complex conjugation inverts every root of
unity (`smul_kummerCoeff_real_eq_neg`, `smul_kummerCoeff_completion_eq_neg`), every first
cohomology group `H¹(G_F, A)` is `2`-torsion. Combining the injective `ℤ/n`-valued invariant with
the order-two and trivial-group duality theorems of
`TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.CyclicTwo` yields:

* **Archimedean local Tate duality in degree one.** For every finite discrete Galois module `A`
  killed by `n`, both `dualityMap1` (`H¹(G_F, A) →+ (H¹(G_F, A') →+ H²(G_F, μₙ))`) and its
  composition with the `ℤ/n`-valued invariant (`realTatePairing`, `infiniteTatePairing`) are
  bijective (`realTatePairing_bijective`, `infiniteTatePairing_bijective`), uniformly at both real
  and complex places.
* **Archimedean local Euler characteristic in degree one.** For every topological Galois module
  `A` killed by `n` over `w.Completion`,
  `Nat.card A ^ w.mult * Nat.card (H¹(G_{K_w}, A)) = Nat.card A^{G_{K_w}} * Nat.card (A')^{G_{K_w}}`
  (`natCard_pow_mult_mul_natCard_H1_completion`), where `w.mult = [K_w : ℝ]` is `1` at a real place
  and `2` at a complex place; `natCard_mul_natCard_H1_real` is the corresponding identity over `ℝ`.

Note that in degrees `0` and `2`, archimedean local Tate duality requires Tate-modified cohomology
`Ĥ⁰` rather than ordinary `H⁰`; degree `1` needs no modification because `Ĥ¹ = H¹`.

## Main definitions

* `TauCeti.ClassFieldTheory.realH2MuToZMod`: the injective normalized invariant
  `H²(G_ℝ, muNRep n ℝ) →+ ZMod n`.
* `TauCeti.ClassFieldTheory.infiniteH2MuToZMod`: the injective normalized invariant
  `H²(G_{K_w}, muNRep n w.Completion) →+ ZMod n` at an infinite place `w`.
* `TauCeti.ClassFieldTheory.realTatePairing`: Tate's degree-one cup-product pairing over `ℝ`
  valued in `ZMod n`.
* `TauCeti.ClassFieldTheory.infiniteTatePairing`: Tate's degree-one cup-product pairing at an
  infinite place `w` valued in `ZMod n`.

## Main results

* `TauCeti.ClassFieldTheory.realH2MuToZMod_injective`,
  `TauCeti.ClassFieldTheory.infiniteH2MuToZMod_injective`: injectivity of the `ℤ/n`-valued
  roots-of-unity invariants.
* `TauCeti.ClassFieldTheory.natCard_absoluteGaloisGroup_real`,
  `TauCeti.ClassFieldTheory.smul_kummerCoeff_real_eq_neg`,
  `TauCeti.ClassFieldTheory.smul_kummerCoeff_completion_eq_neg`: `Gal(ℝˢ/ℝ)` has order `2` and any
  nontrivial automorphism over `ℝ` or `w.Completion` acts by inversion on `μₙ`.
* `TauCeti.ClassFieldTheory.natCard_mul_natCard_H1_real`,
  `TauCeti.ClassFieldTheory.natCard_pow_mult_mul_natCard_H1_completion`: the archimedean local Euler
  characteristic formula in degree one.
* `TauCeti.ClassFieldTheory.dualityMap1_kummerCoeff_real_bijective`,
  `TauCeti.ClassFieldTheory.dualityMap1_kummerCoeff_completion_bijective`: bijectivity of
  `dualityMap1` with coefficients in `μₙ`.
* `TauCeti.ClassFieldTheory.realTatePairing_bijective`,
  `TauCeti.ClassFieldTheory.infiniteTatePairing_bijective`: perfection of the `ℤ/n`-valued
  degree-one Tate pairing over `ℝ` and at every infinite place `w`.

## References

* J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. Internat. Congr.
  Mathematicians (Stockholm, 1962), 288–295.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Theorem 2.13.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.2.17).
-/

public noncomputable section

open NumberField NumberField.InfinitePlace TauCeti ContCohomology

namespace TauCeti.ClassFieldTheory

/-! ### Lifting Brauer invariants on `H²(G_F, μₙ)` to `ZMod n` -/

section BrInvLift

variable {F : Type*} [Field F] [CharZero F] (n : ℕ) [NeZero n]

private theorem nsmul_brInv_h2MuToBr_eq_zero (inv : Br F →+ AddCircle (1 : ℚ))
    (x : continuousCohomology 2 (muNRep n F)) :
    n • inv (h2MuToBr n F x) = 0 := by
  have hn : IsUnit (n : F) := (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit
  rw [← map_nsmul, (h2MuToBr_range n F hn _).mp ⟨x, rfl⟩, map_zero]

private def h2MuToZModFun (inv : Br F →+ AddCircle (1 : ℚ))
    (x : continuousCohomology 2 (muNRep n F)) : ZMod n :=
  (ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero n
    (nsmul_brInv_h2MuToBr_eq_zero n inv x)).choose

private theorem toRatAddCircle_h2MuToZModFun (inv : Br F →+ AddCircle (1 : ℚ))
    (x : continuousCohomology 2 (muNRep n F)) :
    ZMod.toRatAddCircle n (h2MuToZModFun n inv x) = inv (h2MuToBr n F x) :=
  (ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero n
    (nsmul_brInv_h2MuToBr_eq_zero n inv x)).choose_spec

/-- Lift a `ℚ/ℤ`-valued Brauer invariant along `h2MuToBr n F` to a `ZMod n`-valued homomorphism on
`H²(G_F, μₙ)` in characteristic zero. -/
private def h2MuToZModOfBrInv (inv : Br F →+ AddCircle (1 : ℚ)) :
    continuousCohomology 2 (muNRep n F) →+ ZMod n where
  toFun := h2MuToZModFun n inv
  map_zero' := (ZMod.toRatAddCircle_injective n) <| by
    rw [toRatAddCircle_h2MuToZModFun, map_zero, map_zero, map_zero]
  map_add' x y := (ZMod.toRatAddCircle_injective n) <| by
    rw [map_add, toRatAddCircle_h2MuToZModFun, toRatAddCircle_h2MuToZModFun,
      toRatAddCircle_h2MuToZModFun, map_add, map_add]

private theorem toRatAddCircle_h2MuToZModOfBrInv (inv : Br F →+ AddCircle (1 : ℚ))
    (x : continuousCohomology 2 (muNRep n F)) :
    ZMod.toRatAddCircle n (h2MuToZModOfBrInv n inv x) = inv (h2MuToBr n F x) :=
  toRatAddCircle_h2MuToZModFun n inv x

private theorem h2MuToZModOfBrInv_injective {inv : Br F →+ AddCircle (1 : ℚ)}
    (hinv : Function.Injective inv) :
    Function.Injective (h2MuToZModOfBrInv n inv) := by
  have hn : IsUnit (n : F) := (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit
  intro x y hxy
  apply h2MuToBr_injective n F hn
  apply hinv
  rw [← toRatAddCircle_h2MuToZModOfBrInv n inv x, ← toRatAddCircle_h2MuToZModOfBrInv n inv y, hxy]

end BrInvLift

/-! ### Normalized roots-of-unity invariants over `ℝ` and `w.Completion` -/

section RealInvariant

variable (n : ℕ) [NeZero n]

/-- **The normalized real invariant on `H²(G_ℝ, μₙ)`**, valued in `ZMod n`. It is characterized by
`ZMod.toRatAddCircle n (realH2MuToZMod n x) = realInv (h2MuToBr n ℝ x)`: for even `n` it maps the
unique nonzero class to `n / 2`, and for odd `n` the domain is trivial and it is `0`. -/
def realH2MuToZMod : continuousCohomology 2 (muNRep n ℝ) →+ ZMod n :=
  h2MuToZModOfBrInv n realInv

/-- Embedding `realH2MuToZMod` into `ℚ/ℤ` via `k ↦ k / n` recovers the real Brauer invariant of the
Kummer coefficient image. -/
@[simp]
theorem toRatAddCircle_realH2MuToZMod (x : continuousCohomology 2 (muNRep n ℝ)) :
    ZMod.toRatAddCircle n (realH2MuToZMod n x) = realInv (h2MuToBr n ℝ x) :=
  toRatAddCircle_h2MuToZModOfBrInv n realInv x

/-- A class in `H²(G_ℝ, μₙ)` maps to `z : ZMod n` if and only if its real Brauer invariant is the
image of `z` in `ℚ/ℤ`. -/
theorem realH2MuToZMod_eq_iff (x : continuousCohomology 2 (muNRep n ℝ)) (z : ZMod n) :
    realH2MuToZMod n x = z ↔ realInv (h2MuToBr n ℝ x) = ZMod.toRatAddCircle n z := by
  rw [← (ZMod.toRatAddCircle_injective n).eq_iff, toRatAddCircle_realH2MuToZMod]

/-- **The real roots-of-unity invariant into `ZMod n` is injective** for every nonzero `n`. -/
theorem realH2MuToZMod_injective : Function.Injective (realH2MuToZMod n) :=
  h2MuToZModOfBrInv_injective n realInv_injective

/-- Every value of `realH2MuToZMod` is `2`-torsion in `ZMod n`. -/
theorem two_nsmul_realH2MuToZMod (x : continuousCohomology 2 (muNRep n ℝ)) :
    2 • realH2MuToZMod n x = 0 := by
  apply ZMod.toRatAddCircle_injective n
  have hmem : realInv (h2MuToBr n ℝ x) ∈ AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (2 : ℤ) := by
    rw [← SetLike.mem_coe, ← range_realInv]
    exact ⟨_, rfl⟩
  rw [map_nsmul, toRatAddCircle_realH2MuToZMod, AddSubgroup.torsionBy.nsmul_iff.mp hmem, map_zero]

end RealInvariant

section InfiniteInvariant

variable {K : Type*} [Field K] (w : InfinitePlace K) (n : ℕ) [NeZero n]

/-- **The normalized archimedean invariant on `H²(G_{K_w}, μₙ)`**, valued in `ZMod n`. At a real
place it transports `realH2MuToZMod`, and at a complex place it is `0`. -/
def infiniteH2MuToZMod : continuousCohomology 2 (muNRep n w.Completion) →+ ZMod n :=
  have := (Completion.extensionEmbedding w).charZero
  h2MuToZModOfBrInv n (infiniteInvMap w)

/-- Embedding `infiniteH2MuToZMod` into `ℚ/ℤ` via `k ↦ k / n` recovers the archimedean Brauer
invariant of the Kummer coefficient image. -/
@[simp]
theorem toRatAddCircle_infiniteH2MuToZMod
    (x : continuousCohomology 2 (muNRep n w.Completion)) :
    ZMod.toRatAddCircle n (infiniteH2MuToZMod w n x) =
      infiniteInvMap w (h2MuToBr n w.Completion x) := by
  have := (Completion.extensionEmbedding w).charZero
  exact toRatAddCircle_h2MuToZModOfBrInv n (infiniteInvMap w) x

/-- A class in `H²(G_{K_w}, μₙ)` maps to `z : ZMod n` if and only if its archimedean Brauer
invariant is the image of `z` in `ℚ/ℤ`. -/
theorem infiniteH2MuToZMod_eq_iff
    (x : continuousCohomology 2 (muNRep n w.Completion)) (z : ZMod n) :
    infiniteH2MuToZMod w n x = z ↔
      infiniteInvMap w (h2MuToBr n w.Completion x) = ZMod.toRatAddCircle n z := by
  rw [← (ZMod.toRatAddCircle_injective n).eq_iff, toRatAddCircle_infiniteH2MuToZMod]

/-- **The archimedean roots-of-unity invariant into `ZMod n` is injective** at every infinite place,
both real and complex. -/
theorem infiniteH2MuToZMod_injective : Function.Injective (infiniteH2MuToZMod w n) := by
  have := (Completion.extensionEmbedding w).charZero
  exact h2MuToZModOfBrInv_injective n (infiniteInvMap_injective w)

/-- At a complex place, `infiniteH2MuToZMod` is the zero homomorphism. -/
@[simp]
theorem infiniteH2MuToZMod_of_isComplex (hw : w.IsComplex) :
    infiniteH2MuToZMod w n = 0 := by
  ext x
  apply ZMod.toRatAddCircle_injective n
  simp [hw]

/-- Every value of `infiniteH2MuToZMod` is `2`-torsion in `ZMod n`. -/
theorem two_nsmul_infiniteH2MuToZMod
    (x : continuousCohomology 2 (muNRep n w.Completion)) :
    2 • infiniteH2MuToZMod w n x = 0 := by
  rcases w.isReal_or_isComplex with hw | hw
  · apply ZMod.toRatAddCircle_injective n
    have hmem : infiniteInvMap w (h2MuToBr n w.Completion x) ∈
        AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (2 : ℤ) := by
      rw [← SetLike.mem_coe, ← range_infiniteInvMap_of_isReal w hw]
      exact ⟨_, rfl⟩
    rw [map_nsmul, toRatAddCircle_infiniteH2MuToZMod,
      AddSubgroup.torsionBy.nsmul_iff.mp hmem, map_zero]
  · simp [hw]

end InfiniteInvariant

/-! ### Topology and Galois action on `μₙ` over `ℝ` and archimedean completions -/

/-- The absolute Galois group `Gal(ℝˢ/ℝ)` has order two. -/
theorem natCard_absoluteGaloisGroup_real : Nat.card (AbsoluteGaloisGroup ℝ) = 2 := by
  let e := Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  rw [Nat.card_congr e.absoluteGaloisGroupCongr.toEquiv,
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
  have : Finite (AbsoluteGaloisGroup w.Completion) := by
    rcases w.isReal_or_isComplex with hw | hw
    · exact Nat.finite_of_card_ne_zero (by rw [natCard_absoluteGaloisGroup_of_isReal w hw]; decide)
    · have :=
        (Completion.ringEquivComplexOfIsComplex hw).absoluteGaloisGroupCongr.symm
          |>.toEquiv.subsingleton
      infer_instance
  exact Finite.instDiscreteTopology

private theorem smul_kummerCoeff_eq_neg_iff {F : Type*} [Field F] {n : ℕ}
    (g : AbsoluteGaloisGroup F) (y : KummerCoeff F n) :
    g • y = -y ↔
      g (((y.toMul : rootsOfUnity n (SeparableClosure F)) : (SeparableClosure F)ˣ) :
        SeparableClosure F) =
      ((((y.toMul : rootsOfUnity n (SeparableClosure F)) : (SeparableClosure F)ˣ) :
        SeparableClosure F))⁻¹ := by
  constructor
  · intro h
    have h1 := congrArg
      (fun z : KummerCoeff F n =>
        (((z.toMul : rootsOfUnity n (SeparableClosure F)) : (SeparableClosure F)ˣ) :
          SeparableClosure F)) h
    simpa only [Additive.toMul_smul, toMul_neg, rootsOfUnity.coe_smul, Subgroup.coe_inv,
      AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass,
      Units.val_inv_eq_inv_val] using h1
  · intro h
    refine Additive.toMul.injective (Subtype.ext (Units.ext ?_))
    simpa only [Additive.toMul_smul, toMul_neg, rootsOfUnity.coe_smul, Subgroup.coe_inv,
      AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass,
      Units.val_inv_eq_inv_val] using h

private theorem smul_kummerCoeff_congr_eq_neg {F L : Type*} [Field F] [Field L] (e : F ≃+* L)
    {n : ℕ} (hF : ∀ g : AbsoluteGaloisGroup F, g ≠ 1 → ∀ y : KummerCoeff F n, g • y = -y)
    {g : AbsoluteGaloisGroup L} (hg : g ≠ 1) (y : KummerCoeff L n) :
    g • y = -y := by
  have hg' : e.absoluteGaloisGroupCongr g ≠ 1 := fun h =>
    hg (e.absoluteGaloisGroupCongr.injective (h.trans (map_one _).symm))
  let u : (SeparableClosure L)ˣ := (y.toMul : rootsOfUnity n (SeparableClosure L))
  have hu1 : u ^ n = 1 := (mem_rootsOfUnity n u).mp y.toMul.2
  let uF : (SeparableClosure F)ˣ := Units.map e.separableClosureCongr.toRingHom.toMonoidHom u
  have huF : uF ∈ rootsOfUnity n (SeparableClosure F) :=
    (mem_rootsOfUnity n uF).mpr (by rw [← map_pow, hu1, map_one])
  have hval := (smul_kummerCoeff_eq_neg_iff (e.absoluteGaloisGroupCongr g)
    (Additive.ofMul ⟨uF, huF⟩)).mp
    (hF (e.absoluteGaloisGroupCongr g) hg' (Additive.ofMul ⟨uF, huF⟩))
  rw [smul_kummerCoeff_eq_neg_iff]
  apply e.separableClosureCongr.injective
  rw [map_inv₀]
  simpa [u, uF, RingEquiv.absoluteGaloisGroupCongr_apply] using hval

/-- **Complex conjugation inverts every root of unity**: a nontrivial element of `Gal(ℝˢ/ℝ)` acts
on `KummerCoeff ℝ n` by negation. -/
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
  rw [smul_kummerCoeff_eq_neg_iff]
  exact Subtype.ext hinv

/-- **At an infinite place, any nontrivial element of `Gal(K_wˢ/K_w)` inverts every root of unity**
(at a complex place there is no nontrivial element). -/
theorem smul_kummerCoeff_completion_eq_neg {K : Type*} [Field K] (w : InfinitePlace K)
    {n : ℕ} [NeZero n] {g : AbsoluteGaloisGroup w.Completion} (hg : g ≠ 1)
    (y : KummerCoeff w.Completion n) : g • y = -y := by
  rcases w.isReal_or_isComplex with hw | hw
  · exact smul_kummerCoeff_congr_eq_neg (Completion.ringEquivRealOfIsReal hw).symm
      (fun _ h => smul_kummerCoeff_real_eq_neg h) hg y
  · have :=
      (Completion.ringEquivComplexOfIsComplex hw).absoluteGaloisGroupCongr.symm.toEquiv.subsingleton
    exact absurd (Subsingleton.elim g 1) hg

/-! ### Abstract field helpers for degree-one Tate pairings -/

section AbstractFieldDuality

variable {F : Type*} [Field F]

private def tatePairingOfH2MuHom {n : ℕ}
    (ι : continuousCohomology 2 (muNRep n F) →+ ZMod n)
    (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction (AbsoluteGaloisGroup F) A] [ContinuousSMul (AbsoluteGaloisGroup F) A]
    [Finite A] :
    H1 (AbsoluteGaloisGroup F) A →+
      H1 (AbsoluteGaloisGroup F)
        (InternalHom (AbsoluteGaloisGroup F) A (KummerCoeff F n)) →+ ZMod n :=
  (AddMonoidHom.compHom (ι.comp (muNRepH2Equiv n F).toAddMonoidHom)).comp
    (dualityMap1 (AbsoluteGaloisGroup F) A (KummerCoeff F n))

private theorem tatePairingOfH2MuHom_apply {n : ℕ}
    (ι : continuousCohomology 2 (muNRep n F) →+ ZMod n)
    (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction (AbsoluteGaloisGroup F) A] [ContinuousSMul (AbsoluteGaloisGroup F) A]
    [Finite A]
    (x : H1 (AbsoluteGaloisGroup F) A)
    (y : H1 (AbsoluteGaloisGroup F)
      (InternalHom (AbsoluteGaloisGroup F) A (KummerCoeff F n))) :
    tatePairingOfH2MuHom ι A x y =
      ι (muNRepH2Equiv n F (dualityMap1 (AbsoluteGaloisGroup F) A (KummerCoeff F n) x y)) :=
  (rfl)

private theorem toRatAddCircle_tatePairingOfH2MuHom {n : ℕ}
    (ι : continuousCohomology 2 (muNRep n F) →+ ZMod n)
    (inv : Br F →+ AddCircle (1 : ℚ))
    (hι : ∀ z, ZMod.toRatAddCircle n (ι z) = inv (h2MuToBr n F z))
    (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction (AbsoluteGaloisGroup F) A] [ContinuousSMul (AbsoluteGaloisGroup F) A]
    [Finite A]
    (x : H1 (AbsoluteGaloisGroup F) A)
    (y : H1 (AbsoluteGaloisGroup F)
      (InternalHom (AbsoluteGaloisGroup F) A (KummerCoeff F n))) :
    ZMod.toRatAddCircle n (tatePairingOfH2MuHom ι A x y) =
      inv (h2MuToBr n F
        (muNRepH2Equiv n F (dualityMap1 (AbsoluteGaloisGroup F) A (KummerCoeff F n) x y))) := by
  rw [tatePairingOfH2MuHom_apply, hι]

private theorem tatePairingOfH2MuHom_eq_zero {n : ℕ}
    {ι : continuousCohomology 2 (muNRep n F) →+ ZMod n} (hι : ι = 0)
    (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction (AbsoluteGaloisGroup F) A] [ContinuousSMul (AbsoluteGaloisGroup F) A]
    [Finite A] :
    tatePairingOfH2MuHom ι A = 0 := by
  ext x y
  simp [tatePairingOfH2MuHom_apply, hι]

private theorem dualityMap1_kummerCoeff_bijective_of_natCard_eq_two_or_subsingleton
    (hG : Nat.card (AbsoluteGaloisGroup F) = 2 ∨ Subsingleton (AbsoluteGaloisGroup F))
    {n : ℕ} [NeZero n] (hn : IsUnit (n : F))
    {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction (AbsoluteGaloisGroup F) A] [ContinuousSMul (AbsoluteGaloisGroup F) A]
    [Finite A] (hA : ∀ a : A, n • a = 0)
    (hneg : ∀ g : AbsoluteGaloisGroup F, g ≠ 1 → ∀ y : KummerCoeff F n, g • y = -y) :
    Function.Bijective (dualityMap1 (AbsoluteGaloisGroup F) A (KummerCoeff F n)) :=
  hG.elim
    (fun h2 => dualityMap1_bijective_of_natCard_eq_two h2 (kummerCoeffAddEquivZMod hn) hA hneg)
    (fun hsub => dualityMap1_bijective_of_subsingleton hsub)

private theorem tatePairingOfH2MuHom_bijective_of_natCard_eq_two_or_subsingleton
    (hG : Nat.card (AbsoluteGaloisGroup F) = 2 ∨ Subsingleton (AbsoluteGaloisGroup F))
    {n : ℕ} [NeZero n] (hn : IsUnit (n : F))
    {ι : continuousCohomology 2 (muNRep n F) →+ ZMod n} (hι : Function.Injective ι)
    {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction (AbsoluteGaloisGroup F) A] [ContinuousSMul (AbsoluteGaloisGroup F) A]
    [Finite A] (hA : ∀ a : A, n • a = 0)
    (hneg : ∀ g : AbsoluteGaloisGroup F, g ≠ 1 → ∀ y : KummerCoeff F n, g • y = -y) :
    Function.Bijective (tatePairingOfH2MuHom ι A) :=
  hG.elim
    (fun h2 =>
      bijective_compHom_dualityMap1_of_natCard_eq_two h2 (kummerCoeffAddEquivZMod hn) hA hneg
        (ι := ι.comp (muNRepH2Equiv n F).toAddMonoidHom)
        (hι.comp (muNRepH2Equiv n F).injective))
    (fun hsub => bijective_compHom_dualityMap1_of_subsingleton hsub _)

end AbstractFieldDuality

/-! ### Local Euler characteristic and Tate duality over `ℝ` -/

section RealDuality

/-- Every class in `H¹(G_ℝ, A)` is `2`-torsion. -/
theorem two_nsmul_H1_real {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DistribMulAction (AbsoluteGaloisGroup ℝ) A]
    [ContinuousSMul (AbsoluteGaloisGroup ℝ) A] (x : H1 (AbsoluteGaloisGroup ℝ) A) :
    2 • x = 0 :=
  two_nsmul_H1_eq_zero_of_natCard_eq_two natCard_absoluteGaloisGroup_real x

/-- **Real local Euler characteristic in degree one.** For a topological `G_ℝ`-module `A` killed by
`n ≠ 0`, `Nat.card A * Nat.card (H¹(G_ℝ, A)) = Nat.card A^{G_ℝ} * Nat.card (A')^{G_ℝ}` (when `A` is
infinite, both sides are `0`). -/
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

/-- **Tate's degree-one local pairing over `ℝ`**, valued in `ZMod n`: cup product with the dual
module `InternalHom (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n)` followed by `realH2MuToZMod n`. -/
def realTatePairing (n : ℕ) [NeZero n] :
    H1 (AbsoluteGaloisGroup ℝ) A →+
      H1 (AbsoluteGaloisGroup ℝ)
        (InternalHom (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n)) →+ ZMod n :=
  tatePairingOfH2MuHom (realH2MuToZMod n) A

/-- `realTatePairing` evaluates `dualityMap1` and applies the normalized real invariant
`realH2MuToZMod`. -/
@[simp]
theorem realTatePairing_apply (n : ℕ) [NeZero n]
    (x : H1 (AbsoluteGaloisGroup ℝ) A)
    (y : H1 (AbsoluteGaloisGroup ℝ)
      (InternalHom (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n))) :
    realTatePairing A n x y =
      realH2MuToZMod n
        (muNRepH2Equiv n ℝ (dualityMap1 (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n) x y)) :=
  (rfl)

/-- Embedded into `ℚ/ℤ`, `realTatePairing` is the real Brauer invariant of the cup product. -/
theorem toRatAddCircle_realTatePairing (n : ℕ) [NeZero n]
    (x : H1 (AbsoluteGaloisGroup ℝ) A)
    (y : H1 (AbsoluteGaloisGroup ℝ)
      (InternalHom (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n))) :
    ZMod.toRatAddCircle n (realTatePairing A n x y) =
      realInv (h2MuToBr n ℝ
        (muNRepH2Equiv n ℝ (dualityMap1 (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n) x y))) :=
  toRatAddCircle_tatePairingOfH2MuHom (realH2MuToZMod n) realInv
    (toRatAddCircle_realH2MuToZMod n) A x y

variable {A} {n : ℕ} [NeZero n]

/-- Over `ℝ`, `H¹(G_ℝ, A)` and `H¹(G_ℝ, Hom(A, μₙ))` have equal cardinality for every finite
discrete `G_ℝ`-module `A` killed by `n ≠ 0`. -/
theorem natCard_H1_internalHom_kummerCoeff_real (hA : ∀ a : A, n • a = 0) :
    Nat.card (H1 (AbsoluteGaloisGroup ℝ)
      (InternalHom (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n))) =
      Nat.card (H1 (AbsoluteGaloisGroup ℝ) A) :=
  natCard_H1_internalHom_eq_of_natCard_eq_two natCard_absoluteGaloisGroup_real
    (kummerCoeffAddEquivZMod (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit) hA
    (fun _ hg => smul_kummerCoeff_real_eq_neg hg)

/-- **Real local Tate duality in degree one (cohomological target).** For every finite discrete
`G_ℝ`-module `A` killed by `n ≠ 0`, `dualityMap1 (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n)` is
bijective. -/
theorem dualityMap1_kummerCoeff_real_bijective (hA : ∀ a : A, n • a = 0) :
    Function.Bijective (dualityMap1 (AbsoluteGaloisGroup ℝ) A (KummerCoeff ℝ n)) :=
  dualityMap1_kummerCoeff_bijective_of_natCard_eq_two_or_subsingleton
    (Or.inl natCard_absoluteGaloisGroup_real)
    (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit hA
    (fun _ hg => smul_kummerCoeff_real_eq_neg hg)

/-- **Real local Tate duality in degree one (`ℤ/n` target).** For every finite discrete
`G_ℝ`-module `A` killed by `n`, `realTatePairing A n` is bijective: every `ℤ/n`-valued additive
character of `H¹(G_ℝ, Hom(A, μₙ))` is pairing with a unique class of `H¹(G_ℝ, A)`. -/
theorem realTatePairing_bijective (hA : ∀ a : A, n • a = 0) :
    Function.Bijective (realTatePairing A n) :=
  tatePairingOfH2MuHom_bijective_of_natCard_eq_two_or_subsingleton
    (Or.inl natCard_absoluteGaloisGroup_real)
    (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit (realH2MuToZMod_injective n) hA
    (fun _ hg => smul_kummerCoeff_real_eq_neg hg)

end RealDuality

/-! ### Local Euler characteristic and Tate duality at an infinite place -/

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
    (x : H1 (AbsoluteGaloisGroup w.Completion) A) :
    2 • x = 0 := by
  rcases w.isReal_or_isComplex with hw | hw
  · exact two_nsmul_H1_eq_zero_of_natCard_eq_two (natCard_absoluteGaloisGroup_of_isReal w hw) x
  · have :=
      (Completion.ringEquivComplexOfIsComplex hw).absoluteGaloisGroupCongr.symm.toEquiv.subsingleton
    exact Subsingleton.elim _ _

/-- **Archimedean local Euler characteristic in degree one.** For a topological `G_{K_w}`-module `A`
killed by `n ≠ 0`,
`Nat.card A ^ w.mult * Nat.card (H¹(G_{K_w}, A)) = Nat.card A^{G_{K_w}} * Nat.card (A')^{G_{K_w}}`,
where `w.mult = [K_w : ℝ]` is `1` at a real place and `2` at a complex place (when `A` is infinite,
both sides are `0`). -/
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
    exact natCard_mul_natCard_H1_of_natCard_eq_two
      (natCard_absoluteGaloisGroup_of_isReal w hw)
      (kummerCoeffAddEquivZMod hn) hA (fun _ hg => smul_kummerCoeff_completion_eq_neg w hg)
  · have :=
      (Completion.ringEquivComplexOfIsComplex hw).absoluteGaloisGroupCongr.symm.toEquiv.subsingleton
    rw [hw.mult_eq_two]
    exact natCard_sq_mul_natCard_H1_of_subsingleton (kummerCoeffAddEquivZMod hn) hA

variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction (AbsoluteGaloisGroup w.Completion) A]
  [ContinuousSMul (AbsoluteGaloisGroup w.Completion) A] [Finite A]

/-- **Tate's degree-one local pairing at an infinite place `w`**, valued in `ZMod n`: cup product
with the dual module `InternalHom (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n)`
followed by `infiniteH2MuToZMod w n`. -/
def infiniteTatePairing (n : ℕ) [NeZero n] :
    H1 (AbsoluteGaloisGroup w.Completion) A →+
      H1 (AbsoluteGaloisGroup w.Completion)
        (InternalHom (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n)) →+ ZMod n :=
  tatePairingOfH2MuHom (infiniteH2MuToZMod w n) A

/-- `infiniteTatePairing` evaluates `dualityMap1` and applies the normalized archimedean invariant
`infiniteH2MuToZMod w n`. -/
@[simp]
theorem infiniteTatePairing_apply (n : ℕ) [NeZero n]
    (x : H1 (AbsoluteGaloisGroup w.Completion) A)
    (y : H1 (AbsoluteGaloisGroup w.Completion)
      (InternalHom (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n))) :
    infiniteTatePairing w A n x y =
      infiniteH2MuToZMod w n
        (muNRepH2Equiv n w.Completion
          (dualityMap1 (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n) x y)) :=
  (rfl)

/-- Embedded into `ℚ/ℤ`, `infiniteTatePairing` is the archimedean Brauer invariant of the cup
product. -/
theorem toRatAddCircle_infiniteTatePairing (n : ℕ) [NeZero n]
    (x : H1 (AbsoluteGaloisGroup w.Completion) A)
    (y : H1 (AbsoluteGaloisGroup w.Completion)
      (InternalHom (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n))) :
    ZMod.toRatAddCircle n (infiniteTatePairing w A n x y) =
      infiniteInvMap w (h2MuToBr n w.Completion
        (muNRepH2Equiv n w.Completion
          (dualityMap1 (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n) x y))) :=
  toRatAddCircle_tatePairingOfH2MuHom (infiniteH2MuToZMod w n) (infiniteInvMap w)
    (toRatAddCircle_infiniteH2MuToZMod w n) A x y

/-- At a complex place, `infiniteTatePairing` is the zero homomorphism (between trivial `H¹`
groups). -/
@[simp]
theorem infiniteTatePairing_of_isComplex (hw : w.IsComplex) (n : ℕ) [NeZero n] :
    infiniteTatePairing w A n = 0 :=
  tatePairingOfH2MuHom_eq_zero (infiniteH2MuToZMod_of_isComplex w n hw) A

variable {A} {n : ℕ} [NeZero n]

/-- At any infinite place `w`, `H¹(G_{K_w}, A)` and `H¹(G_{K_w}, Hom(A, μₙ))` have equal
cardinality for every finite discrete `G_{K_w}`-module `A` killed by `n ≠ 0`. -/
theorem natCard_H1_internalHom_kummerCoeff_completion (hA : ∀ a : A, n • a = 0) :
    Nat.card (H1 (AbsoluteGaloisGroup w.Completion)
      (InternalHom (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n))) =
      Nat.card (H1 (AbsoluteGaloisGroup w.Completion) A) := by
  have := (Completion.extensionEmbedding w).charZero
  have hn : IsUnit (n : w.Completion) := (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit
  rcases w.isReal_or_isComplex with hw | hw
  · exact natCard_H1_internalHom_eq_of_natCard_eq_two
      (natCard_absoluteGaloisGroup_of_isReal w hw)
      (kummerCoeffAddEquivZMod hn) hA (fun _ hg => smul_kummerCoeff_completion_eq_neg w hg)
  · have :=
      (Completion.ringEquivComplexOfIsComplex hw).absoluteGaloisGroupCongr.symm.toEquiv.subsingleton
    have h1 : Subsingleton (H1 (AbsoluteGaloisGroup w.Completion) A) :=
      subsingleton_H1_of_subsingleton _ _
    have h2 : Subsingleton (H1 (AbsoluteGaloisGroup w.Completion)
        (InternalHom (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n))) :=
      subsingleton_H1_of_subsingleton _ _
    rw [Nat.card_eq_one_iff_unique.mpr ⟨h2, ⟨0⟩⟩, Nat.card_eq_one_iff_unique.mpr ⟨h1, ⟨0⟩⟩]

/-- **Archimedean local Tate duality in degree one (cohomological target).** At any infinite place
`w`, for every finite discrete `G_{K_w}`-module `A` killed by `n ≠ 0`,
`dualityMap1 (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n)` is bijective. -/
theorem dualityMap1_kummerCoeff_completion_bijective (hA : ∀ a : A, n • a = 0) :
    Function.Bijective
      (dualityMap1 (AbsoluteGaloisGroup w.Completion) A (KummerCoeff w.Completion n)) := by
  have := (Completion.extensionEmbedding w).charZero
  exact dualityMap1_kummerCoeff_bijective_of_natCard_eq_two_or_subsingleton
    (natCard_eq_two_or_subsingleton_completion w)
    (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit hA
    (fun _ hg => smul_kummerCoeff_completion_eq_neg w hg)

/-- **Archimedean local Tate duality in degree one (`ℤ/n` target).** At any infinite place `w`, for
every finite discrete `G_{K_w}`-module `A` killed by `n`, `infiniteTatePairing w A n` is bijective:
every `ℤ/n`-valued additive character of `H¹(G_{K_w}, Hom(A, μₙ))` is pairing with a unique class of
`H¹(G_{K_w}, A)`. -/
theorem infiniteTatePairing_bijective (hA : ∀ a : A, n • a = 0) :
    Function.Bijective (infiniteTatePairing w A n) := by
  have := (Completion.extensionEmbedding w).charZero
  exact tatePairingOfH2MuHom_bijective_of_natCard_eq_two_or_subsingleton
    (natCard_eq_two_or_subsingleton_completion w)
    (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit (infiniteH2MuToZMod_injective w n) hA
    (fun _ hg => smul_kummerCoeff_completion_eq_neg w hg)

end InfiniteDuality

end TauCeti.ClassFieldTheory
