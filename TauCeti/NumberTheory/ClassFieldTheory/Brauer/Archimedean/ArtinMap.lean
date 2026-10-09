/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Archimedean.ClassFormation
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.AbsoluteArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.NormSubgroup
public import TauCeti.NumberTheory.ClassFieldTheory.UnitsLayer
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Extension
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Norm

/-!
# The archimedean Artin maps

Let `w` be an infinite place of a field `K`, with completion `K_w`, which is `ℝ` or `ℂ`. The
units formation of `K_w` carries the class formation `infiniteClassFormation w`, whose invariant is
the archimedean Brauer invariant `infiniteInvMap w` after inflation. Its absolute Artin map, read
through the identification of the ground level with `K_wˣ` and the comparison of the separable and
algebraic closures, is the **archimedean Artin map**

```text
infiniteArtinAt w : K_wˣ →* G_{K_w}^ab,
```

into the topological abelianization of Mathlib's absolute Galois group, the target of the
nonarchimedean `artinMap`. It is built from the formation machinery and the archimedean Brauer
computation alone, with no reciprocity law.

On every layer `V ◁ G_{K_w}` it is the abstract Artin map of `infiniteClassFormation w`
(`infiniteArtinAt_layer`), so the character formula of a class formation gives the archimedean
character formula `χ(Art_w x) = inv_w(x ∪ δχ)` (`character_infiniteArtinAt`). This is the form in
which an archimedean Artin symbol enters a sum of local invariants.

The map is explicit. At a complex place `G_{K_w}` is trivial, so `Art_w` is trivial
(`infiniteArtinAt_eq_one_of_isComplex`). At a real place `G_{K_w}` has order two, so `Art_w` kills
the squares, which are the positive elements, while the Artin map of the quadratic layer is
surjective onto a group of order two; hence the kernel of `Art_w` is exactly `ℝ_{>0}`, the norm
group of `ℂ/ℝ` (`infiniteArtinAt_eq_one_iff_of_isReal`). On roots of unity a lift of `Art_w(x)`
therefore acts trivially for `x > 0` and by `ζ ↦ ζ⁻¹` for `x < 0`, that is, through the explicit
real cyclotomic symbol `realCyclotomicSymbol` (`infiniteArtinAt_rootsOfUnity_of_isReal`): the
nontrivial automorphism of `K_w(i)/K_w` sends `a + b i` to `a - b i`, so `ζ σ(ζ) = a² + b²` is a
nonnegative root of unity in `K_w ≅ ℝ`. Finally, the archimedean Artin maps are functorial for the
norm of a finite extension (`infiniteArtinAt_norm`), the archimedean analogue of `artinMap_norm`.

## Main definitions

* `TauCeti.ClassFieldTheory.infiniteArtinAt`: the archimedean Artin map `K_wˣ →* G_{K_w}^ab`.

## Main results

* `TauCeti.ClassFieldTheory.infiniteArtinAt_layer`: on every layer `V ◁ G_{K_w}`, the archimedean
  Artin map is the Artin map of `infiniteClassFormation w`.
* `TauCeti.ClassFieldTheory.character_infiniteArtinAt`: the archimedean character formula.
* `TauCeti.ClassFieldTheory.infiniteArtinAt_eq_one_of_isComplex`: at a complex place the Artin map
  is trivial.
* `TauCeti.ClassFieldTheory.infiniteArtinAt_eq_one_iff_of_isReal`: at a real place the kernel of
  the Artin map is the group of positive elements.
* `TauCeti.ClassFieldTheory.infiniteArtinAt_rootsOfUnity_of_isReal`: at a real place the Artin
  symbol acts on the `m`-th roots of unity through `realCyclotomicSymbol m`.
* `TauCeti.ClassFieldTheory.infiniteArtinAt_norm`: norm functoriality of the archimedean Artin
  maps.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§1–4.
* J. S. Milne, *Class Field Theory*, Chapter VII, §8 (the local Artin symbol at an archimedean
  place), and Chapter VIII, §4.
-/

public noncomputable section

open NumberField NumberField.InfinitePlace

namespace TauCeti.ClassFieldTheory

open NormalLayer

variable {K : Type} [Field K]

/-- The **archimedean Artin map** `Art_w : K_wˣ →* G_{K_w}^ab` at an infinite place `w`: the
absolute Artin map of `infiniteClassFormation w`, read on `K_wˣ` and in the topological
abelianization of Mathlib's absolute Galois group of `K_w`. On every layer it is the Artin map of
that class formation (`infiniteArtinAt_layer`); it is trivial at a complex place
(`infiniteArtinAt_eq_one_of_isComplex`) and has kernel the positive elements at a real place
(`infiniteArtinAt_eq_one_iff_of_isReal`). -/
def infiniteArtinAt (w : InfinitePlace K) :
    w.Completionˣ →* Field.absoluteGaloisGroupAbelianization w.Completion :=
  (absoluteGaloisGroupRestrictEquiv w.Completion).symm.topologicalAbelianizationCongr.toMonoidHom
    |>.comp (MonoidHom.toAdditive.symm
      ((infiniteClassFormation w).absoluteArtinMap.comp
        (unitsLevelEquiv (Algebra.ofId w.Completion (SeparableClosure w.Completion))
          (fixedField_toSubgroup_top w.Completion)).toAddMonoidHom))

/-- **The archimedean Artin map is the absolute Artin map of `infiniteClassFormation w`**: the
absolute Artin symbol of `x ∈ K_wˣ`, regarded as an element of the ground level, carried from
`Gal(K_wˢ/K_w)^ab` to `Gal(AlgebraicClosure K_w/K_w)^ab`. -/
theorem infiniteArtinAt_apply (w : InfinitePlace K) (x : w.Completionˣ) :
    infiniteArtinAt w x =
      (absoluteGaloisGroupRestrictEquiv w.Completion).symm.topologicalAbelianizationCongr
        ((infiniteClassFormation w).absoluteArtinMap
          (unitsLevelEquiv (Algebra.ofId w.Completion (SeparableClosure w.Completion))
            (fixedField_toSubgroup_top w.Completion) (Additive.ofMul x))).toMul := by
  rw [infiniteArtinAt, MonoidHom.comp_apply, MonoidHom.toAdditive_symm_apply_apply]
  rfl

/-- If `σ ∈ Gal(AlgebraicClosure K_w/K_w)` represents `Art_w(x)`, then the absolute Artin symbol
of `x` for `infiniteClassFormation w` is the class of the restriction of `σ` to the separable
closure. -/
private theorem absoluteArtinMap_eq_of_mk_eq_infiniteArtinAt (w : InfinitePlace K)
    (x : w.Completionˣ) (σ : Field.absoluteGaloisGroup w.Completion)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization w.Completion) = infiniteArtinAt w x) :
    (infiniteClassFormation w).absoluteArtinMap
        (unitsLevelEquiv (Algebra.ofId w.Completion (SeparableClosure w.Completion))
          (fixedField_toSubgroup_top w.Completion) (Additive.ofMul x)) =
      Additive.ofMul ((absoluteGaloisGroupRestrictEquiv w.Completion σ :
        AbsoluteGaloisGroup w.Completion) :
          TopologicalAbelianization (AbsoluteGaloisGroup w.Completion)) := by
  rw [← ContinuousMulEquiv.topologicalAbelianizationCongr_mk, hσ, infiniteArtinAt_apply,
    ← ContinuousMulEquiv.topologicalAbelianizationCongr_symm,
    ContinuousMulEquiv.apply_symm_apply, ofMul_toMul]

/-- **The archimedean Artin map on a layer.** If `σ ∈ Gal(AlgebraicClosure K_w/K_w)` represents
`Art_w(x)`, then for every open normal subgroup `V` of `G_{K_w}` the Artin map of
`infiniteClassFormation w` on the layer `V ◁ G_{K_w}` sends `x` to the class of the restriction of
`σ`. -/
theorem infiniteArtinAt_layer (w : InfinitePlace K)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion)) (x : w.Completionˣ)
    (σ : Field.absoluteGaloisGroup w.Completion)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization w.Completion) = infiniteArtinAt w x) :
    (infiniteClassFormation w).artinMap (ofOpenNormal V)
        (localGroundEquiv w.Completion V (Additive.ofMul x)) =
      Additive.ofMul (Abelianization.of ((galOfOpenNormalEquiv V).symm
        (absoluteGaloisGroupRestrictEquiv w.Completion σ :
          AbsoluteGaloisGroup w.Completion ⧸ V.toSubgroup))) := by
  have hground : groundEquivOfOpenNormal (unitsFormation w.Completion) V
      (unitsLevelEquiv (Algebra.ofId w.Completion (SeparableClosure w.Completion))
        (fixedField_toSubgroup_top w.Completion) (Additive.ofMul x)) =
      localGroundEquiv w.Completion V (Additive.ofMul x) :=
    Subtype.ext (by simp)
  have hmem : (absoluteGaloisGroupRestrictEquiv w.Completion σ : AbsoluteGaloisGroup w.Completion)
      ∈ (ofOpenNormal V).ground := by
    simp
  have hsymm : (galOfOpenNormalEquiv V).symm
      (absoluteGaloisGroupRestrictEquiv w.Completion σ :
        AbsoluteGaloisGroup w.Completion ⧸ V.toSubgroup) =
      ((⟨_, hmem⟩ : (ofOpenNormal V).ground) : (ofOpenNormal V).Gal) := by
    rw [MulEquiv.symm_apply_eq, galOfOpenNormalEquiv_mk]
  rw [← hground, ← ClassFormation.abelianizationRestrict_absoluteArtinMap,
    absoluteArtinMap_eq_of_mk_eq_infiniteArtinAt w x σ hσ, abelianizationRestrict_mk V ⟨_, hmem⟩,
    hsymm]

/-- **The archimedean character formula** `χ(Art_w x) = inv_w(x ∪ δχ)`. If `σ` represents
`Art_w(x)`, then for every character `χ` of the abelianized Galois group of a layer
`V ◁ G_{K_w}`, the value of `χ` at the class of `σ` is the archimedean Brauer invariant of the
inflation of the cup product of `x` with the connecting class of `χ`. -/
theorem character_infiniteArtinAt (w : InfinitePlace K)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion)) (x : w.Completionˣ)
    (σ : Field.absoluteGaloisGroup w.Completion)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization w.Completion) = infiniteArtinAt w x)
    (χ : Additive (Abelianization (ofOpenNormal V).Gal) →+ AddCircle (1 : ℚ)) :
    χ (Additive.ofMul (Abelianization.of ((galOfOpenNormalEquiv V).symm
        (absoluteGaloisGroupRestrictEquiv w.Completion σ :
          AbsoluteGaloisGroup w.Completion ⧸ V.toSubgroup)))) =
      infiniteInvMap w (brInfl V ((ofOpenNormal V).artinCharacterCup
        (unitsFormation w.Completion) (localGroundEquiv w.Completion V (Additive.ofMul x)) χ)) :=
  (congrArg χ (infiniteArtinAt_layer w V x σ hσ)).symm.trans
    (((infiniteClassFormation w).character_artinMap (ofOpenNormal V) _ χ).symm.trans
      (infiniteClassFormation_inv w V _))

/-- An element killed by the archimedean Artin map is a norm from every layer: its Artin symbol
for `infiniteClassFormation w` vanishes on every layer `V ◁ G_{K_w}`. -/
private theorem artinMap_eq_zero_of_infiniteArtinAt_eq_one (w : InfinitePlace K)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion)) {x : w.Completionˣ}
    (hx : infiniteArtinAt w x = 1) :
    (infiniteClassFormation w).artinMap (ofOpenNormal V)
      (localGroundEquiv w.Completion V (Additive.ofMul x)) = 0 := by
  rw [infiniteArtinAt_layer w V x 1 (by rw [hx, QuotientGroup.mk_one]), map_one,
    QuotientGroup.mk_one, map_one, map_one, ofMul_one]

/-- At a complex place `Gal(AlgebraicClosure K_w/K_w)` is trivial. -/
private theorem subsingleton_fieldAbsoluteGaloisGroup_of_isComplex (w : InfinitePlace K)
    (hw : w.IsComplex) : Subsingleton (Field.absoluteGaloisGroup w.Completion) :=
  have := subsingleton_absoluteGaloisGroup_of_isComplex w hw
  (absoluteGaloisGroupRestrictEquiv w.Completion).toEquiv.subsingleton

/-- **The archimedean Artin map is trivial at a complex place**: the absolute Galois group of
`K_w ≅ ℂ` is trivial. -/
@[simp]
theorem infiniteArtinAt_eq_one_of_isComplex (w : InfinitePlace K) (hw : w.IsComplex)
    (x : w.Completionˣ) : infiniteArtinAt w x = 1 := by
  have := subsingleton_fieldAbsoluteGaloisGroup_of_isComplex w hw
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (infiniteArtinAt w x)
  rw [← hσ, Subsingleton.elim σ 1, QuotientGroup.mk_one]

section Real

variable (w : InfinitePlace K) (hw : w.IsReal)
include hw

/-- At a real place `Gal(AlgebraicClosure K_w/K_w)` has order two. -/
private theorem natCard_fieldAbsoluteGaloisGroup_of_isReal :
    Nat.card (Field.absoluteGaloisGroup w.Completion) = 2 := by
  rw [Nat.card_congr (absoluteGaloisGroupRestrictEquiv w.Completion).toEquiv,
    natCard_absoluteGaloisGroup_of_isReal w hw]

/-- At a real place `Gal(AlgebraicClosure K_w/K_w)` has order two, as a group of automorphisms. -/
private theorem natCard_gal_of_isReal :
    Nat.card Gal(AlgebraicClosure w.Completion/w.Completion) = 2 :=
  natCard_fieldAbsoluteGaloisGroup_of_isReal w hw

/-- A real completion `K_w ≅ ℝ` has characteristic zero. -/
private theorem charZero_of_isReal : CharZero w.Completion :=
  charZero_of_injective_ringHom (f := (Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
    (Completion.ringEquivRealOfIsReal hw).symm.injective

/-- At a real place every element of `G_{K_w}^ab` squares to `1`, since `G_{K_w}` has order two. -/
private theorem sq_eq_one_of_isReal (y : Field.absoluteGaloisGroupAbelianization w.Completion) :
    y ^ 2 = 1 := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_pow, ← natCard_fieldAbsoluteGaloisGroup_of_isReal w hw,
    pow_card_eq_one', QuotientGroup.mk_one]

open scoped IsMulCommutative in
/-- At a real place some element has nontrivial Artin symbol: the Artin map of the quadratic layer
is surjective onto the abelianization of a group of order two. -/
private theorem exists_infiniteArtinAt_ne_one_of_isReal :
    ∃ x : w.Completionˣ, infiniteArtinAt w x ≠ 1 := by
  set V := realOpenNormalSubgroup w hw
  have hcard : Nat.card (ofOpenNormal V).Gal = 2 :=
    (ofOpenNormal V).degree_eq_natCard_gal.symm.trans (degree_realLayer w hw)
  have : Fact (Nat.card (ofOpenNormal V).Gal).Prime := ⟨hcard ▸ Nat.prime_two⟩
  have : IsCyclic (ofOpenNormal V).Gal := isCyclic_of_prime_card rfl
  have : Nontrivial (ofOpenNormal V).Gal := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have : Nontrivial (Abelianization (ofOpenNormal V).Gal) :=
    Abelianization.equivOfComm.injective.nontrivial
  obtain ⟨y, hy⟩ := exists_ne (0 : Additive (Abelianization (ofOpenNormal V).Gal))
  obtain ⟨a, ha⟩ := (infiniteClassFormation w).surjective_artinMap (ofOpenNormal V) y
  obtain ⟨x, rfl⟩ := (localGroundEquiv w.Completion V).surjective a
  exact ⟨x.toMul, fun hx ↦ hy (ha ▸ artinMap_eq_zero_of_infiniteArtinAt_eq_one w V hx)⟩

/-- At a real place an automorphism of `AlgebraicClosure K_w` with trivial class in `G_{K_w}^ab` is
the identity: `G_{K_w}` has order two, so its closed commutator subgroup is trivial. -/
private theorem eq_one_of_mk_eq_one_of_isReal {σ : Field.absoluteGaloisGroup w.Completion}
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization w.Completion) = 1) : σ = 1 := by
  have : Fact (Nat.card (Field.absoluteGaloisGroup w.Completion)).Prime :=
    ⟨natCard_fieldAbsoluteGaloisGroup_of_isReal w hw ▸ Nat.prime_two⟩
  have : IsCyclic (Field.absoluteGaloisGroup w.Completion) := isCyclic_of_prime_card rfl
  have hclosure :
      (commutator (Field.absoluteGaloisGroup w.Completion)).topologicalClosure = ⊥ := by
    rw [commutator_eq_bot]
    exact le_bot_iff.mp (Subgroup.topologicalClosure_minimal _ le_rfl isClosed_singleton)
  have hmem := (QuotientGroup.eq_one_iff σ).mp hσ
  rwa [hclosure, Subgroup.mem_bot] at hmem

/-- At a real place an element of `AlgebraicClosure K_w` fixed by a nontrivial automorphism lies in
`K_w`: that automorphism and the identity are all of `G_{K_w}`, which has order two. -/
private theorem mem_range_algebraMap_of_isReal {σ : Gal(AlgebraicClosure w.Completion/w.Completion)}
    (hσ : σ ≠ 1) {y : AlgebraicClosure w.Completion} (hy : σ y = y) :
    y ∈ Set.range (algebraMap w.Completion (AlgebraicClosure w.Completion)) := by
  have := charZero_of_isReal w hw
  refine IntermediateField.mem_bot.mp ((InfiniteGalois.mem_bot_iff_fixed y).mpr fun τ ↦ ?_)
  by_cases hτ : τ = 1
  · rw [hτ, AlgEquiv.one_apply]
  · rwa [((Nat.card_eq_two_iff' 1).mp (natCard_gal_of_isReal w hw)).unique hτ hσ]

/-- At a real place a nontrivial automorphism of `AlgebraicClosure K_w` inverts every root of
unity: writing `z = a + b i` with `a, b ∈ K_w`, the product `z σ(z) = a² + b²` is a nonnegative root
of unity in `K_w ≅ ℝ`, hence `1`. -/
private theorem apply_eq_inv_of_isReal {σ : Gal(AlgebraicClosure w.Completion/w.Completion)}
    (hσ : σ ≠ 1) {m : ℕ} (hm : m ≠ 0) {z : AlgebraicClosure w.Completion} (hz : z ^ m = 1) :
    σ z = z⁻¹ := by
  let ι := algebraMap w.Completion (AlgebraicClosure w.Completion)
  have := charZero_of_isReal w hw
  have hσσ (y : AlgebraicClosure w.Completion) : σ (σ y) = y := by
    rw [← AlgEquiv.mul_apply, ← sq, ← natCard_gal_of_isReal w hw, pow_card_eq_one',
      AlgEquiv.one_apply]
  -- `K_w ≅ ℝ` has no square root of `-1`, but its algebraic closure has one, `i`, with `σ i = -i`.
  have hnsq (c : w.Completion) : c ^ 2 ≠ -1 := fun hc ↦ by
    have h := congrArg (Completion.extensionEmbeddingOfIsReal hw) hc
    rw [map_pow, map_neg, map_one] at h
    nlinarith [sq_nonneg (Completion.extensionEmbeddingOfIsReal hw c)]
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure w.Completion) two_pos
  have hσi : σ i = -i := by
    have h2 : σ i ^ 2 = i ^ 2 := by rw [← map_pow, hi, map_neg, map_one]
    refine (sq_eq_sq_iff_eq_or_eq_neg.mp h2).resolve_left fun h ↦ ?_
    obtain ⟨c, hc⟩ := mem_range_algebraMap_of_isReal w hw hσ h
    exact hnsq c (ι.injective (by rw [map_pow, hc, hi, map_neg, map_one]))
  have hi0 : i ≠ 0 := by
    rintro rfl
    norm_num at hi
  -- The real and imaginary parts of `z` are fixed by `σ`, so they lie in `K_w`.
  obtain ⟨a, ha⟩ := mem_range_algebraMap_of_isReal w hw hσ (y := (z + σ z) / 2) (by
    rw [map_div₀, map_add, hσσ, map_ofNat, add_comm])
  obtain ⟨b, hb⟩ := mem_range_algebraMap_of_isReal w hw hσ (y := (z - σ z) / (2 * i)) (by
    rw [map_div₀, map_sub, map_mul, hσσ, map_ofNat, hσi, mul_neg, div_neg, ← neg_div, neg_sub])
  have hzz : z * σ z = ι (a ^ 2 + b ^ 2) := by
    rw [map_add, map_pow, map_pow, ha, hb, div_pow, div_pow, mul_pow, hi]
    ring
  -- `a² + b²` is a nonnegative root of unity in `K_w`, hence `1`.
  have hpow : (a ^ 2 + b ^ 2) ^ m = 1 := ι.injective <| by
    rw [map_pow, ← hzz, mul_pow, ← map_pow, hz, map_one, one_mul, map_one]
  have hone : Completion.extensionEmbeddingOfIsReal hw (a ^ 2 + b ^ 2) = 1 :=
    (pow_eq_one_iff_of_nonneg (by simp only [map_add, map_pow]; positivity) hm).mp
      (by rw [← map_pow, hpow, map_one])
  have h1 : a ^ 2 + b ^ 2 = 1 :=
    (Completion.extensionEmbeddingOfIsReal hw).injective (hone.trans (map_one _).symm)
  rw [h1, map_one] at hzz
  exact eq_inv_of_mul_eq_one_right hzz

/-- At a real place any two nontrivial elements of `G_{K_w}^ab` are equal, since `G_{K_w}` has
order two. -/
private theorem eq_of_ne_one_of_isReal
    {a b : Field.absoluteGaloisGroupAbelianization w.Completion} (ha : a ≠ 1) (hb : b ≠ 1) :
    a = b := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective b
  have hσ : σ ≠ 1 := by
    rintro rfl
    exact ha (QuotientGroup.mk_one _)
  have hτ : τ ≠ 1 := by
    rintro rfl
    exact hb (QuotientGroup.mk_one _)
  rw [((Nat.card_eq_two_iff' 1).mp (natCard_fieldAbsoluteGaloisGroup_of_isReal w hw)).unique hσ hτ]

/-- **The kernel of the real Artin map is `ℝ_{>0}`**: at a real place, `Art_w(x)` is trivial
exactly when the image of `x` in `ℝ` is positive, so that the kernel is the norm group of
`ℂ/ℝ`. -/
theorem infiniteArtinAt_eq_one_iff_of_isReal (x : w.Completionˣ) :
    infiniteArtinAt w x = 1 ↔ 0 < Completion.extensionEmbeddingOfIsReal hw (x : w.Completion) := by
  -- Positive elements are squares, so they are killed by `Art_w`.
  have hpos (y : w.Completionˣ) (hy : 0 < Completion.extensionEmbeddingOfIsReal hw y) :
      infiniteArtinAt w y = 1 := by
    obtain ⟨r, hr⟩ := Completion.surjective_extensionEmbeddingOfIsReal hw
      (Real.sqrt (Completion.extensionEmbeddingOfIsReal hw y))
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [map_zero, eq_comm, Real.sqrt_eq_zero hy.le] at hr
      exact hy.ne' hr
    have hsq : Units.mk0 r hr0 ^ 2 = y := Units.ext <|
      (Completion.extensionEmbeddingOfIsReal hw).injective <| by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hr, Real.sq_sqrt hy.le]
    rw [← hsq, map_pow, sq_eq_one_of_isReal w hw]
  refine ⟨fun hx ↦ ?_, hpos x⟩
  by_contra hneg
  -- If a negative element were killed, so would be every element: each is either positive or
  -- that element times a positive one.
  obtain ⟨y, hy⟩ := exists_infiniteArtinAt_ne_one_of_isReal w hw
  refine hy ?_
  have hx0 : Completion.extensionEmbeddingOfIsReal hw x < 0 :=
    lt_of_le_of_ne (not_lt.mp hneg) (map_ne_zero _ |>.mpr x.ne_zero)
  rcases (map_ne_zero (Completion.extensionEmbeddingOfIsReal hw) |>.mpr y.ne_zero).lt_or_gt
    with hyneg | hypos
  · have hq : 0 < Completion.extensionEmbeddingOfIsReal hw ↑(x⁻¹ * y) := by
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      exact mul_pos_of_neg_of_neg (inv_lt_zero.mpr hx0) hyneg
    rw [← mul_inv_cancel_left x y, map_mul, hx, hpos _ hq, one_mul]
  · exact hpos y hypos

/-- **The real Artin map on roots of unity.** At a real place, a lift `σ` of `Art_w(x)` acts on the
`m`-th roots of unity through `realCyclotomicSymbol m` at the image of `x` in `ℝ`: trivially for
`x > 0`, and by `ζ ↦ ζ⁻¹`, complex conjugation, for `x < 0`. -/
theorem infiniteArtinAt_rootsOfUnity_of_isReal (m : ℕ) [NeZero m] (x : w.Completionˣ)
    (σ : Field.absoluteGaloisGroup w.Completion)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization w.Completion) = infiniteArtinAt w x)
    {z : AlgebraicClosure w.Completion} (hz : z ^ m = 1) :
    σ.toRingEquiv z = z ^ ((realCyclotomicSymbol m
      (Units.map (Completion.extensionEmbeddingOfIsReal hw).toMonoidHom x) : ZMod m).val) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  rcases (map_ne_zero (Completion.extensionEmbeddingOfIsReal hw) |>.mpr x.ne_zero).lt_or_gt
    with hneg | hpos
  · have hσ1 : σ ≠ 1 := by
      rintro rfl
      rw [QuotientGroup.mk_one, eq_comm, infiniteArtinAt_eq_one_iff_of_isReal w hw] at hσ
      exact hσ.not_gt hneg
    rw [realCyclotomicSymbol_of_neg _ _ (by simpa using hneg), Units.val_neg, Units.val_one,
      ZMod.val_neg_one]
    exact (apply_eq_inv_of_isReal w hw hσ1 n.succ_ne_zero hz).trans
      (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hz])).symm
  · have hσ1 : σ = 1 := eq_one_of_mk_eq_one_of_isReal w hw
      (hσ.trans ((infiniteArtinAt_eq_one_iff_of_isReal w hw x).mpr hpos))
    rw [realCyclotomicSymbol_of_pos _ _ (by simpa using hpos), Units.val_one,
      ZMod.val_one_eq_one_mod]
    -- `σ.toRingEquiv` applies `σ`, so for `σ = 1` it is the identity.
    calc σ.toRingEquiv z = z := by subst hσ1; rfl
      _ = z ^ (1 % (n + 1)) := by
        rcases n with _ | n
        · simpa using hz
        · rw [Nat.one_mod_eq_one.mpr (by omega), pow_one]

end Real

section Norm

open scoped NumberField.LiesOver

variable {L : Type} [Field L] [Algebra K L]

/-- **Norm functoriality at the archimedean places**, the analogue of `artinMap_norm`: for a place
`w` of `L` over `v`, embedded by `iota`, the image in `G_{K_v}^ab` of a lift of `Art_w(x)` is
`Art_v(N_{L_w/K_v} x)`. For `ℝ/ℝ` the norm is the identity, and for `ℂ/ℝ` and `ℂ/ℂ` both sides are
trivial, `N(x) = |x|²` being positive in the first case. -/
theorem infiniteArtinAt_norm (w : InfinitePlace L) (v : InfinitePlace K) [w.LiesOver v]
    [Module.Finite v.Completion w.Completion]
    (iota : w.Completion →ₐ[v.Completion] SeparableClosure v.Completion) (x : w.Completionˣ)
    (τ : Field.absoluteGaloisGroup w.Completion)
    (hτ : (τ : Field.absoluteGaloisGroupAbelianization w.Completion) = infiniteArtinAt w x) :
    (absoluteGaloisGroupExtend v.Completion w.Completion iota τ :
        Field.absoluteGaloisGroupAbelianization v.Completion) =
      infiniteArtinAt v
        (Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) x) := by
  rcases v.isReal_or_isComplex with hv | hv
  · rcases w.isReal_or_isComplex with hw | hw
    · -- `ℝ/ℝ`: the norm is the identity, so both sides are trivial for the same `x`.
      have hLHS : (absoluteGaloisGroupExtend v.Completion w.Completion iota τ :
          Field.absoluteGaloisGroupAbelianization v.Completion) = 1 ↔
            infiniteArtinAt w x = 1 := by
        rw [← hτ]
        refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
        · rw [injective_absoluteGaloisGroupExtend v.Completion w.Completion iota
            ((eq_one_of_mk_eq_one_of_isReal v hv h).trans (map_one _).symm), QuotientGroup.mk_one]
        · rw [eq_one_of_mk_eq_one_of_isReal w hw h, map_one, QuotientGroup.mk_one]
      have hRHS : infiniteArtinAt v (Units.map (Algebra.norm v.Completion :
          w.Completion →* v.Completion) x) = 1 ↔ infiniteArtinAt w x = 1 := by
        rw [infiniteArtinAt_eq_one_iff_of_isReal v hv, infiniteArtinAt_eq_one_iff_of_isReal w hw,
          Units.coe_map, Completion.extensionEmbeddingOfIsReal_norm_of_isReal hv hw]
      by_cases h1 : infiniteArtinAt w x = 1
      · rw [hLHS.mpr h1, hRHS.mpr h1]
      · exact eq_of_ne_one_of_isReal v hv (fun h ↦ h1 (hLHS.mp h)) (fun h ↦ h1 (hRHS.mp h))
    · -- `ℂ/ℝ`: `G_{K_w}` is trivial, and the norm `|x|²` is positive.
      have := subsingleton_fieldAbsoluteGaloisGroup_of_isComplex w hw
      have hram : w.IsRamified K := isRamified_iff.mpr ⟨hw, (LiesOver.comap_eq w v).symm ▸ hv⟩
      rw [Subsingleton.elim τ 1, map_one, QuotientGroup.mk_one, eq_comm,
        infiniteArtinAt_eq_one_iff_of_isReal v hv, Units.coe_map,
        Completion.extensionEmbeddingOfIsReal_norm_of_isRamified hram hv]
      exact Complex.normSq_pos.mpr ((map_ne_zero _).mpr x.ne_zero)
  · -- `ℂ/ℂ`: `G_{K_v}` is trivial.
    have := subsingleton_fieldAbsoluteGaloisGroup_of_isComplex v hv
    rw [infiniteArtinAt_eq_one_of_isComplex v hv,
      Subsingleton.elim (absoluteGaloisGroupExtend v.Completion w.Completion iota τ) 1,
      QuotientGroup.mk_one]

end Norm

end TauCeti.ClassFieldTheory
