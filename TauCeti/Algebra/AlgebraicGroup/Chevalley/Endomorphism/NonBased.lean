/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.Standard
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Equalizer
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Conjugation

/-!
# Weyl-twisted Frobenius and non-based standard endomorphisms of Chevalley data

Composing `D.frobenius p k A` with conjugation by `n_i = D.weylElement (t.simpleIndex ht i) A 1`
produces an endomorphism `D.weylFrobenius i p k A` of `D.points A` with character map
`(p ^ k : ℕ) • D.simpleReflectionCharacterMap i` (`isCharacterMap_weylFrobenius`). Over any perfect
ring `A` of exponential characteristic `p`, `D.weylFrobenius i p k A` is **standard**
(`isStandard_weylFrobenius`), while over any nontrivial commutative ring of exponential
characteristic `p` it fails to preserve `D.borelSubgroup A`
(`not_map_borelSubgroup_weylFrobenius_le`) and is therefore **not based**
(`not_isBased_weylFrobenius`). Simple Weyl conjugation itself is likewise standard over every
commutative ring (`isStandard_conj_weylElement`) and non-based over every nontrivial one
(`not_isBased_conj_weylElement`).

In general rank, `(D.weylFrobenius i p k A).comp (D.weylFrobenius i p k A)` equals
`MulAut.conj (D.simpleCorootPoints i A (-1)) ∘ D.frobenius p (k + k) A`
(`weylFrobenius_comp_weylFrobenius`). In rank one (`t.rank = 1`, covering `SL₂`, `PGL₂`, and every
faithful integral `𝔰𝔩₂`-datum), `D.simpleReflectionCharacterMap i = -1`
(`simpleReflectionCharacterMap_eq_neg_one_of_rank_eq_one`), every root has even pairing `±2` with
`α_i^∨`, so `D.simpleCorootPoints i A (-1)` centralizes the closed subgroup scheme `D.groupScheme`
(`simpleCorootPoints_neg_one_conj_eq_self_of_rank_eq_one`), and
`(D.weylFrobenius i p k A).comp (D.weylFrobenius i p k A) = D.frobenius p (k + k) A` holds on the
entire point group `D.points A` (`weylFrobenius_comp_weylFrobenius_of_rank_eq_one`).

## References

* R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, Mem. Amer. Math. Soc. **80** (1968),
  §§10–11.
* G. Malle and D. Testerman, *Linear Algebraic Groups and Finite Groups of Lie Type*, Cambridge
  Univ. Press (2011), §21.1 and Example 22.3.
-/

public section

open Multiplicative

namespace TauCeti.DynkinType.ChevalleyDatum

noncomputable section

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ## The character map of a simple reflection on the actual weight lattice -/

/-- The `ℤ`-linear endomorphism of `Fin t.rank → ℤ` representing the simple reflection `s_i` in the
chosen basis `D.weightLatticeBasis` of `D.weightLattice`: it sends `χ` to
`χ - ⟨D.weightLatticeEmbedding χ, α_i^∨⟩ • D.coordinateRoot α_i`. -/
def simpleReflectionCharacterMap (i : Fin t.rank) : Module.End ℤ (Fin t.rank → ℤ) :=
  LinearMap.id -
    (LinearMap.proj i ∘ₗ D.weightLatticeEmbedding).smulRight (D.coordinateRoot (t.simpleIndex ht i))

/-- Explicit coordinate formula for `D.simpleReflectionCharacterMap i`. -/
@[simp]
theorem simpleReflectionCharacterMap_apply (i : Fin t.rank) (χ : Fin t.rank → ℤ) :
    D.simpleReflectionCharacterMap i χ =
      χ - (D.weightLatticeEmbedding χ i) • D.coordinateRoot (t.simpleIndex ht i) := by rfl

/-- Under `D.weightLatticeEmbedding`, `D.simpleReflectionCharacterMap i` subtracts the `i`-th
fundamental-weight coordinate times the `i`-th simple root. -/
theorem weightLatticeEmbedding_simpleReflectionCharacterMap (i : Fin t.rank)
    (χ : Fin t.rank → ℤ) :
    D.weightLatticeEmbedding (D.simpleReflectionCharacterMap i χ) =
      D.weightLatticeEmbedding χ -
        (D.weightLatticeEmbedding χ i) •
          (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i) := by
  rw [simpleReflectionCharacterMap_apply, map_sub, map_smul,
    D.weightLatticeEmbedding_coordinateRoot]

/-- The simple reflection character map negates its own simple coordinate root. -/
theorem simpleReflectionCharacterMap_coordinateRoot_simpleIndex (i : Fin t.rank) :
    D.simpleReflectionCharacterMap i (D.coordinateRoot (t.simpleIndex ht i)) =
      -D.coordinateRoot (t.simpleIndex ht i) := by
  have hp : (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i) i = 2 := by simp
  rw [simpleReflectionCharacterMap_apply, D.weightLatticeEmbedding_coordinateRoot, hp]
  module

/-- `D.simpleReflectionCharacterMap i` is an involutive `ℤ`-linear map. -/
theorem simpleReflectionCharacterMap_involutive (i : Fin t.rank) :
    Function.Involutive (D.simpleReflectionCharacterMap i) := fun χ => by
  have hp : (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i) i = 2 := by simp
  calc D.simpleReflectionCharacterMap i (D.simpleReflectionCharacterMap i χ)
    _ = χ - (D.weightLatticeEmbedding χ i) • D.coordinateRoot (t.simpleIndex ht i) -
          (D.weightLatticeEmbedding χ i - D.weightLatticeEmbedding χ i * 2) •
            D.coordinateRoot (t.simpleIndex ht i) := by
      rw [simpleReflectionCharacterMap_apply, D.weightLatticeEmbedding_simpleReflectionCharacterMap,
        Pi.sub_apply, Pi.smul_apply, hp, smul_eq_mul, simpleReflectionCharacterMap_apply]
    _ = χ := by module

/-- Squaring `D.simpleReflectionCharacterMap i` in `Module.End ℤ (Fin t.rank → ℤ)` gives `1`. -/
@[simp]
theorem simpleReflectionCharacterMap_mul_self (i : Fin t.rank) :
    D.simpleReflectionCharacterMap i * D.simpleReflectionCharacterMap i = 1 :=
  LinearMap.ext (D.simpleReflectionCharacterMap_involutive i)

/-- `D.simpleReflectionCharacterMap i` is bijective. -/
theorem simpleReflectionCharacterMap_bijective (i : Fin t.rank) :
    Function.Bijective (D.simpleReflectionCharacterMap i) :=
  (D.simpleReflectionCharacterMap_involutive i).bijective

/-- `D.simpleReflectionCharacterMap i` is injective. -/
theorem simpleReflectionCharacterMap_injective (i : Fin t.rank) :
    Function.Injective (D.simpleReflectionCharacterMap i) :=
  (D.simpleReflectionCharacterMap_involutive i).injective

/-- **The torus map induced by `D.simpleReflectionCharacterMap i` is
`D.simpleReflectionTorusParameter i A`**, over every commutative ring `A`. -/
@[simp]
theorem torusPointMap_simpleReflectionCharacterMap (i : Fin t.rank) (A : Type v) [CommRing A] :
    torusPointMap (R := A) (D.simpleReflectionCharacterMap i) =
      D.simpleReflectionTorusParameter i A := by
  refine MonoidHom.ext fun s => funext fun j => ?_
  rw [torusPointMap_apply, simpleReflectionCharacterMap_apply, D.weightLatticeEmbedding_single,
    torusCharacter_sub, torusCharacter_zsmul, torusCharacter_single, zpow_one,
    D.simpleReflectionTorusParameter_apply]

/-- **In rank one (`t.rank = 1`), `D.simpleReflectionCharacterMap i` is `-1`**, regardless of
whether `D.weightLattice` is the full weight lattice (`SL₂`), the root lattice (`PGL₂`), or any
intermediate lattice. -/
theorem simpleReflectionCharacterMap_eq_neg_one_of_rank_eq_one (hr : t.rank = 1)
    (i : Fin t.rank) : D.simpleReflectionCharacterMap i = -1 := by
  refine LinearMap.ext fun χ => D.weightLatticeEmbedding_injective (funext fun j => ?_)
  obtain rfl : j = i := Fin.ext (by omega)
  have hp : (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht j) j = 2 := by simp
  rw [D.weightLatticeEmbedding_simpleReflectionCharacterMap, Pi.sub_apply, Pi.smul_apply,
    hp, smul_eq_mul, LinearMap.neg_apply, one_apply_eq_self, map_neg, Pi.neg_apply]
  ring

/-! ## Simple Weyl conjugation as a standard non-based endomorphism -/

section WeylConj

variable (i : Fin t.rank) (A : Type v) [CommRing A]

/-- Conjugation by the pinned simple Weyl element `D.weylElement (t.simpleIndex ht i) A 1` has
character map `D.simpleReflectionCharacterMap i` on `D.torusPoints A`. -/
theorem isCharacterMap_conj_weylElement :
    IsCharacterMap (D.torusPoints A)
      (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1) : D.points A →* D.points A)
      (D.simpleReflectionCharacterMap i) :=
  isCharacterMap_iff.mpr fun s => by
    rw [MonoidHom.coe_ofClass, MulAut.conj_apply,
      D.weylElement_conj_torusPoints, D.torusPointMap_simpleReflectionCharacterMap]

/-- Conjugation by `D.weylElement (t.simpleIndex ht i) A 1` maps each root subgroup onto the
reflected root subgroup, over every commutative ring `A`. -/
@[simp]
theorem map_range_rootSubgroupPoints_conj_weylElement (γ : Fin t.numRoots) :
    (D.rootSubgroupPoints γ A).range.map
        (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1) : D.points A →* D.points A) =
      (D.rootSubgroupPoints
        ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ) A).range := by
  let ε : ℤˣ := t.chevalleyWeylSign ht (t.simpleIndex ht i) γ
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    refine ⟨ofAdd (((ε : ℤ) : A) * toAdd u), ?_⟩
    rw [MonoidHom.coe_ofClass, MulAut.conj_apply]
    conv_rhs => rw [← ofAdd_toAdd u, D.weylElement_conj_rootSubgroupPoints]
  · rintro _ ⟨u, rfl⟩
    refine ⟨D.rootSubgroupPoints γ A (ofAdd ((((ε⁻¹ : ℤˣ) : ℤ) : A) * toAdd u)), ⟨_, rfl⟩, ?_⟩
    have hε : ((ε : ℤ) : A) * (((ε⁻¹ : ℤˣ) : ℤ) : A) = 1 := by
      rw [← Int.cast_mul, Units.mul_inv, Int.cast_one]
    rw [MonoidHom.coe_ofClass, MulAut.conj_apply,
      D.weylElement_conj_rootSubgroupPoints, ← mul_assoc, hε, one_mul, ofAdd_toAdd]

/-- Conjugation by a pinned simple Weyl representative is standard over every commutative ring. -/
theorem isStandard_conj_weylElement :
    D.IsStandard
      (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1) : D.points A →* D.points A) :=
  (D.isStandard_def _).mpr
    ⟨⟨D.simpleReflectionCharacterMap i, D.simpleReflectionCharacterMap_injective i,
        D.isCharacterMap_conj_weylElement i A⟩,
      fun γ => ⟨_, D.map_range_rootSubgroupPoints_conj_weylElement i A γ⟩⟩

/-- Over any nontrivial commutative ring, conjugation by a pinned simple Weyl representative is not
based because it sends a positive simple-root element outside `D.borelSubgroup A`. -/
theorem not_isBased_conj_weylElement [Nontrivial A] :
    ¬ D.IsBased
      (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1) : D.points A →* D.points A) :=
  fun hBased => by
    obtain ⟨b, hb⟩ := D.exists_weylElement_conj_notMem_borelSubgroup A i
    exact hb (hBased.map_borelSubgroup_le ⟨b.1, b.2, rfl⟩)

end WeylConj

/-! ## Weyl-twisted Frobenius endomorphisms -/

section WeylFrobenius

/-- Frobenius fixes the pinned Weyl element `D.weylElement γ A 1` at unit parameter `1`. -/
@[simp]
theorem frobenius_weylElement_one (γ : Fin t.numRoots) (p k : ℕ) (A : Type v)
    [CommRing A] [ExpChar A p] :
    D.frobenius p k A (D.weylElement γ A 1) = D.weylElement γ A 1 :=
  Subtype.ext (by rw [coe_frobenius, map_weylElement, map_one])

/-- **The Weyl-twisted Frobenius endomorphism `Int(n_i(1)) ∘ Frob_{p^k}` on `D.points A`**, defined
for any node `i : Fin t.rank` and commutative ring `A` of exponential characteristic `p`. -/
def weylFrobenius (i : Fin t.rank) (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p] :
    D.points A →* D.points A :=
  (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1) : D.points A →* D.points A).comp
    (D.frobenius p k A)

/-- Unfolding formula for `D.weylFrobenius i p k A`. -/
theorem weylFrobenius_apply (i : Fin t.rank) (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]
    (g : D.points A) :
    D.weylFrobenius i p k A g =
      D.weylElement (t.simpleIndex ht i) A 1 * D.frobenius p k A g *
        (D.weylElement (t.simpleIndex ht i) A 1)⁻¹ := (rfl)

/-- On `D.torusPoints A`, `D.weylFrobenius i p k A` raises parameters to `p ^ k` and applies the
simple reflection `D.simpleReflectionTorusParameter i A`. -/
@[simp]
theorem weylFrobenius_torusPoints (i : Fin t.rank) (p k : ℕ) (A : Type v)
    [CommRing A] [ExpChar A p] (s : Fin t.rank → Aˣ) :
    D.weylFrobenius i p k A (D.torusPoints A s) =
      D.torusPoints A (D.simpleReflectionTorusParameter i A (s ^ p ^ k)) := by
  rw [weylFrobenius_apply, D.frobenius_torusPoints, D.weylElement_conj_torusPoints]

/-- On the `γ`-root subgroup, `D.weylFrobenius i p k A` raises the parameter to `p ^ k` and
transports to `s_i(γ)` with the Chevalley Weyl sign. -/
@[simp]
theorem weylFrobenius_rootSubgroupPoints (i : Fin t.rank) (p k : ℕ) (A : Type v)
    [CommRing A] [ExpChar A p] (γ : Fin t.numRoots) (u : A) :
    D.weylFrobenius i p k A (D.rootSubgroupPoints γ A (ofAdd u)) =
      D.rootSubgroupPoints
        ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ) A
        (ofAdd (((t.chevalleyWeylSign ht (t.simpleIndex ht i) γ : ℤ) : A) * u ^ p ^ k)) := by
  rw [weylFrobenius_apply, D.frobenius_rootSubgroupPoints, D.weylElement_conj_rootSubgroupPoints]

/-- **Character map of `D.weylFrobenius i p k A`**: on `D.torusPoints A`, its character pullback is
`(p ^ k : ℕ) • D.simpleReflectionCharacterMap i`. -/
theorem isCharacterMap_weylFrobenius (i : Fin t.rank) (p k : ℕ) (A : Type v)
    [CommRing A] [ExpChar A p] :
    IsCharacterMap (D.torusPoints A) (D.weylFrobenius i p k A)
      ((p ^ k : ℕ) • D.simpleReflectionCharacterMap i) := by
  simpa only [weylFrobenius, smul_mul_assoc, one_mul] using
    (D.isCharacterMap_conj_weylElement i A).comp (D.isCharacterMap_frobenius p k A)

/-- **In rank one (`t.rank = 1`), the character map of `D.weylFrobenius i p k A` is
`-((p ^ k : ℕ) • 1)`.** -/
theorem isCharacterMap_weylFrobenius_of_rank_eq_one (hr : t.rank = 1) (i : Fin t.rank)
    (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p] :
    IsCharacterMap (D.torusPoints A) (D.weylFrobenius i p k A) (-((p ^ k : ℕ) • 1)) := by
  have h := D.isCharacterMap_weylFrobenius i p k A
  rwa [D.simpleReflectionCharacterMap_eq_neg_one_of_rank_eq_one hr i, smul_neg] at h

/-- Over a perfect ring `A` of exponential characteristic `p`, `D.weylFrobenius i p k A` maps each
root subgroup `γ` onto the reflected root subgroup `s_i(γ)`. -/
@[simp]
theorem map_range_rootSubgroupPoints_weylFrobenius (i : Fin t.rank) (p k : ℕ) (A : Type v)
    [CommRing A] [ExpChar A p] [PerfectRing A p] (γ : Fin t.numRoots) :
    (D.rootSubgroupPoints γ A).range.map (D.weylFrobenius i p k A) =
      (D.rootSubgroupPoints
        ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ) A).range := by
  rw [weylFrobenius, ← Subgroup.map_map, D.map_range_rootSubgroupPoints_frobenius p k γ,
    D.map_range_rootSubgroupPoints_conj_weylElement]

/-- **Over any perfect ring of exponential characteristic `p`, `D.weylFrobenius i p k A` is
standard.** -/
theorem isStandard_weylFrobenius (i : Fin t.rank) (p k : ℕ) (A : Type v)
    [CommRing A] [ExpChar A p] [PerfectRing A p] :
    D.IsStandard (D.weylFrobenius i p k A) :=
  (D.isStandard_conj_weylElement i A).comp (D.isStandard_frobenius p k)

/-- **Over any nontrivial commutative ring of exponential characteristic `p`,
`D.weylFrobenius i p k A` does not preserve `D.borelSubgroup A`**, witnessed by `x_{α_i}(1)`. -/
theorem not_map_borelSubgroup_weylFrobenius_le (i : Fin t.rank) (p k : ℕ) (A : Type v)
    [CommRing A] [Nontrivial A] [ExpChar A p] :
    ¬ (D.borelSubgroup A).map (D.weylFrobenius i p k A) ≤ D.borelSubgroup A := fun hle => by
  have hpos := support_subset_posRoots (t.rationalRootSystem ht) (t.rationalBase ht)
    (t.simpleIndex_mem_support i)
  have himg : D.weylFrobenius i p k A
      (D.rootSubgroupPoints (t.simpleIndex ht i) A (ofAdd 1)) ∈ D.borelSubgroup A :=
    hle ⟨_, D.positivePoints_le_borelSubgroup A
      (D.rootSubgroupPoints_mem_positivePoints A hpos (ofAdd 1)), rfl⟩
  rw [weylFrobenius_apply, D.frobenius_rootSubgroupPoints, one_pow,
    D.weylElement_conj_rootSubgroupPoints_simpleIndex_mem_borelSubgroup_iff] at himg
  exact D.rootSubgroupPoints_ofAdd_one_ne_one A (t.simpleIndex ht i) himg

/-- **Over any nontrivial commutative ring of exponential characteristic `p`,
`D.weylFrobenius i p k A` is not based.** -/
theorem not_isBased_weylFrobenius (i : Fin t.rank) (p k : ℕ) (A : Type v)
    [CommRing A] [Nontrivial A] [ExpChar A p] :
    ¬ D.IsBased (D.weylFrobenius i p k A) := fun h =>
  D.not_map_borelSubgroup_weylFrobenius_le i p k A h.map_borelSubgroup_le

/-- **Square of `D.weylFrobenius i p k A` in general rank**: composing `D.weylFrobenius i p k A`
with itself gives `D.frobenius p (k + k) A` followed by conjugation by
`D.simpleCorootPoints i A (-1)` on `D.points A`. -/
theorem weylFrobenius_comp_weylFrobenius (i : Fin t.rank) (p k : ℕ) (A : Type v)
    [CommRing A] [ExpChar A p] :
    (D.weylFrobenius i p k A).comp (D.weylFrobenius i p k A) =
      (MulAut.conj (D.simpleCorootPoints i A (-1)) : D.points A →* D.points A).comp
        (D.frobenius p (k + k) A) := by
  refine MonoidHom.ext fun g => ?_
  simp only [MonoidHom.comp_apply, weylFrobenius_apply, map_mul, map_inv,
    D.frobenius_weylElement_one, MonoidHom.coe_ofClass, MulAut.conj_apply]
  rw [show D.frobenius p k A (D.frobenius p k A g) = D.frobenius p (k + k) A g by
    rw [D.frobenius_add, MonoidHom.comp_apply], ← D.weylElement_mul_self i A]
  group

end WeylFrobenius

end

end ChevalleyDatum

/-! ## Rank-one root classification and scheme-level centrality of `α_i^∨(-1)` -/

private theorem eq_A_one_of_rank_eq_one {t : DynkinType} (ht : t.Valid) (hr : t.rank = 1) :
    t = .A 1 := by
  cases t
  case A n => rw [rank_A] at hr; subst hr; rfl
  case B n => rw [rank_B] at hr; have := valid_B.mp ht; omega
  case C n => rw [rank_C] at hr; have := valid_C.mp ht; omega
  case D n => rw [rank_D] at hr; have := valid_D.mp ht; omega
  all_goals simp at hr

/-- In rank one (`t.rank = 1`), every root index is either the unique simple root
`t.simpleIndex ht i` or its negative `reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i)`. -/
theorem eq_simpleIndex_or_reflectionPerm_of_rank_eq_one {t : DynkinType} (ht : t.Valid)
    (hr : t.rank = 1) (i : Fin t.rank) (γ : Fin t.numRoots) :
    γ = t.simpleIndex ht i ∨
      γ = (t.simplyConnectedRootDatum ht).reflectionPerm
        (t.simpleIndex ht i) (t.simpleIndex ht i) := by
  let P := t.simplyConnectedRootDatum ht
  let α := t.simpleIndex ht i
  let β := P.reflectionPerm α α
  have hcard : Fintype.card (Fin t.numRoots) = 2 := by
    rw [Fintype.card_fin, eq_A_one_of_rank_eq_one ht hr]; rfl
  have hα : P.root α i = 2 := by simp [P, α]
  have hβ : P.root β i = -2 := by
    have href := congrFun (P.reflectionPerm_root α α) i
    rw [Pi.sub_apply, Pi.smul_apply, P.root_coroot_two α, hα, smul_eq_mul] at href
    dsimp only [β]; omega
  have hne : α ≠ β := fun h => by have := congrArg (fun δ => P.root δ i) h; omega
  have huniv : ({α, β} : Finset (Fin t.numRoots)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, hcard])
  have hmem : γ ∈ ({α, β} : Finset (Fin t.numRoots)) := by rw [huniv]; exact Finset.mem_univ γ
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

namespace ChevalleyDatum

noncomputable section

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

private theorem mem_hopfIdealPointsSubgroup_equalizer_conjCoordinateIso_iff {n : ℕ}
    (C : Matrix.GeneralLinearGroup (Fin n) ℤ) (A : Type v) [CommRing A]
    (M : Matrix.GeneralLinearGroup (Fin n) A) :
    M ∈ GeneralLinear.hopfIdealPointsSubgroup n
        (CommHopfAlgCat.equalizerHopfIdeal (GeneralLinear.conjCoordinateIso C).hom
          (CategoryTheory.CategoryStruct.id (GeneralLinear.coordinateHopfAlgebra ℤ n))) A ↔
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) C * M *
          (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) C)⁻¹ = M := by
  let H₀ := GeneralLinear.coordinateHopfAlgebra ℤ n
  let J := CommHopfAlgCat.equalizerHopfIdeal (GeneralLinear.conjCoordinateIso C).hom
    (CategoryTheory.CategoryStruct.id H₀)
  let f := (GeneralLinear.pointsMulEquiv (R := ℤ) n).symm M
  rw [GeneralLinear.mem_hopfIdealPointsSubgroup_iff,
    show (∀ x ∈ J, f.ofConv x = 0) ↔ J.toIdeal ≤ RingHom.ker f.ofConv.toRingHom from
      ⟨fun h _ hx => RingHom.mem_ker.mpr (h _ hx), fun h _ hx => RingHom.mem_ker.mp (h hx)⟩,
    CommHopfAlgCat.equalizerHopfIdeal_le_ker_iff (GeneralLinear.conjCoordinateIso C).hom
      (CategoryTheory.CategoryStruct.id H₀) f.ofConv.toRingHom]
  refine ⟨fun h => ?_, fun h a => ?_⟩
  · simpa only [GeneralLinear.pointsMulEquiv_toConv_comp_conjCoordinateIso, f,
      MulEquiv.apply_symm_apply] using congrArg (GeneralLinear.pointsMulEquiv n)
      (WithConv.ofConv_injective (AlgHom.ext h) : WithConv.toConv (f.ofConv.comp
        ((GeneralLinear.conjCoordinateIso C).hom.hom : H₀ →ₐ[ℤ] H₀)) = f)
  · have hpt : GeneralLinear.pointsMulEquiv n (WithConv.toConv (f.ofConv.comp
        ((GeneralLinear.conjCoordinateIso C).hom.hom : H₀ →ₐ[ℤ] H₀))) =
        GeneralLinear.pointsMulEquiv n f := by
      simpa only [GeneralLinear.pointsMulEquiv_toConv_comp_conjCoordinateIso, f,
        MulEquiv.apply_symm_apply] using h
    exact AlgHom.congr_fun
      (congrArg WithConv.ofConv ((GeneralLinear.pointsMulEquiv n).injective hpt)) a

private theorem simpleCorootPoints_neg_one_conj_rootSubgroupPoints_of_rank_eq_one
    (hr : t.rank = 1) (i : Fin t.rank) (A : Type v) [CommRing A] (γ : Fin t.numRoots)
    (u : Multiplicative A) :
    D.simpleCorootPoints i A (-1) * D.rootSubgroupPoints γ A u *
        (D.simpleCorootPoints i A (-1))⁻¹ = D.rootSubgroupPoints γ A u := by
  rw [D.simpleCorootPoints_eq_torusPoints, ← ofAdd_toAdd u, D.torusPoints_conj_rootSubgroupPoints,
    D.coordinateRoot_def,
    D.torusCharacter_simpleCorootParameter i A (-1) ⟨_, D.root_mem_weightLattice γ⟩]
  have hone : (-1 : Aˣ) ^ ((t.simplyConnectedRootDatum ht).root γ i) = 1 := by
    rcases t.eq_simpleIndex_or_reflectionPerm_of_rank_eq_one ht hr i γ with rfl | rfl
    · rw [show (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i) i = 2 by simp]; simp
    · have hp : (t.simplyConnectedRootDatum ht).root
          ((t.simplyConnectedRootDatum ht).reflectionPerm
            (t.simpleIndex ht i) (t.simpleIndex ht i)) i = -2 := by
        rw [← D.weightLatticeEmbedding_coordinateRoot, D.coordinateRoot_reflectionPerm_self,
          map_neg, D.weightLatticeEmbedding_coordinateRoot, Pi.neg_apply]; simp
      rw [hp, zpow_neg]; simp
  rw [hone, Units.val_one, one_mul]

private theorem map_algebraMap_int_simpleCorootPoints_neg_one (i : Fin t.rank)
    (B : Type v) [CommRing B] :
    Matrix.GeneralLinearGroup.map (algebraMap ℤ B)
        (D.simpleCorootPoints i ℤ (-1) : Matrix.GeneralLinearGroup (Fin D.dim) ℤ) =
      (D.simpleCorootPoints i B (-1) : Matrix.GeneralLinearGroup (Fin D.dim) B) := by
  rw [D.map_simpleCorootPoints, show Units.map (algebraMap ℤ B).toMonoidHom (-1 : ℤˣ) = (-1 : Bˣ)
    from Units.ext (by simp)]

/-- Simple coroot points centralize every torus point in the commutative split torus. -/
theorem simpleCorootPoints_conj_torusPoints (i : Fin t.rank) (A : Type v) [CommRing A]
    (u : Aˣ) (s : Fin t.rank → Aˣ) :
    D.simpleCorootPoints i A u * D.torusPoints A s * (D.simpleCorootPoints i A u)⁻¹ =
      D.torusPoints A s := by
  rw [D.simpleCorootPoints_eq_torusPoints, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (D.torusPoints A) (by ext j; simp [mul_comm])

/-- **In rank one (`t.rank = 1`), `D.simpleCorootPoints i A (-1)` is central in `D.points A` over
every commutative ring `A`.** Since `α_i^∨(-1)` centralizes every root subgroup and every torus
point functorially over commutative rings, the closed subgroup scheme `D.groupScheme` lies inside
its centralizer in `GLₙ`. -/
theorem simpleCorootPoints_neg_one_conj_eq_self_of_rank_eq_one (hr : t.rank = 1) (i : Fin t.rank)
    (A : Type v) [CommRing A] (g : D.points A) :
    D.simpleCorootPoints i A (-1) * g * (D.simpleCorootPoints i A (-1))⁻¹ = g := by
  let C : Matrix.GeneralLinearGroup (Fin D.dim) ℤ := D.simpleCorootPoints i ℤ (-1)
  have hg : (g : Matrix.GeneralLinearGroup (Fin D.dim) A) ∈
      UniversalEnvelopingAlgebra.kostantToralPointsSubgroup (t.lieBasis ht).rootGenerator
        (t.lieBasis ht).h D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator D.basis D.coordinateWeight A := by
    rw [← D.points_eq_kostantToralPointsSubgroup]; exact g.2
  have hmem :=
    UniversalEnvelopingAlgebra.conj_mem_hopfIdealPointsSubgroup_of_mem_kostantToralPointsSubgroup
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator D.basis
      D.coordinateWeight
      (CommHopfAlgCat.equalizerHopfIdeal (GeneralLinear.conjCoordinateIso C).hom
        (CategoryTheory.CategoryStruct.id (GeneralLinear.coordinateHopfAlgebra ℤ D.dim))) 1
      (fun B _ k q => by
        rw [map_one, one_mul, inv_one, mul_one,
          mem_hopfIdealPointsSubgroup_equalizer_conjCoordinateIso_iff,
          D.map_algebraMap_int_simpleCorootPoints_neg_one i B]
        let u : Multiplicative B := AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := B) q
        have hq : q = (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := B)).symm u :=
          (MulEquiv.symm_apply_apply _ _).symm
        rcases k with m | m
        · rw [hq, ← D.coe_rootSubgroupPoints_simpleIndex m B u]
          simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val
            (D.simpleCorootPoints_neg_one_conj_rootSubgroupPoints_of_rank_eq_one hr i B _ u)
        · rw [hq, ← D.coe_rootSubgroupPoints_reflectionPerm_simpleIndex m B u]
          simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val
            (D.simpleCorootPoints_neg_one_conj_rootSubgroupPoints_of_rank_eq_one hr i B _ u))
      (fun B _ s => by
        rw [map_one, one_mul, inv_one, mul_one,
          mem_hopfIdealPointsSubgroup_equalizer_conjCoordinateIso_iff,
          D.map_algebraMap_int_simpleCorootPoints_neg_one i B, ← D.coe_torusPoints B s]
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
          congrArg Subtype.val (D.simpleCorootPoints_conj_torusPoints i B (-1) s)) A hg
  rw [map_one, one_mul, inv_one, mul_one,
    mem_hopfIdealPointsSubgroup_equalizer_conjCoordinateIso_iff,
    D.map_algebraMap_int_simpleCorootPoints_neg_one i A] at hmem
  exact Subtype.ext hmem

/-- **In rank one (`t.rank = 1`), the square of `D.weylFrobenius i p k A` equals
`D.frobenius p (k + k) A` on the entire point group `D.points A`**, over every commutative ring `A`
of exponential characteristic `p`. -/
theorem weylFrobenius_comp_weylFrobenius_of_rank_eq_one (hr : t.rank = 1)
    (i : Fin t.rank) (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p] :
    (D.weylFrobenius i p k A).comp (D.weylFrobenius i p k A) = D.frobenius p (k + k) A := by
  refine MonoidHom.ext fun g => ?_
  rw [D.weylFrobenius_comp_weylFrobenius, MonoidHom.comp_apply,
    MonoidHom.coe_ofClass, MulAut.conj_apply]
  exact D.simpleCorootPoints_neg_one_conj_eq_self_of_rank_eq_one hr i A _

/-- Pointwise form of `weylFrobenius_comp_weylFrobenius_of_rank_eq_one`. -/
theorem weylFrobenius_weylFrobenius_eq_frobenius_of_rank_eq_one (hr : t.rank = 1)
    (i : Fin t.rank) (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p] (g : D.points A) :
    D.weylFrobenius i p k A (D.weylFrobenius i p k A g) = D.frobenius p (k + k) A g :=
  DFunLike.congr_fun (D.weylFrobenius_comp_weylFrobenius_of_rank_eq_one hr i p k A) g

end

end ChevalleyDatum

end TauCeti.DynkinType
