/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Center
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.Standard
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne

/-!
# Weyl-twisted Frobenius and non-based standard endomorphisms of Chevalley data

`D.weylFrobenius i p k A` composes `D.frobenius p k A` with conjugation by
`n_i = D.weylElement (t.simpleIndex ht i) A 1`. Its character map is
`(p ^ k : ℕ) • D.simpleReflectionCharacterMap i` (`isCharacterMap_weylFrobenius`); it is standard
over every perfect ring (`isStandard_weylFrobenius`), and neither it nor simple Weyl conjugation is
based over any nontrivial ring (`not_isBased_weylFrobenius`, `not_isBased_conj_weylElement`). Its
square is `Int(α_i^∨(-1)) ∘ D.frobenius p (k + k) A` (`weylFrobenius_comp_weylFrobenius`), which
equals `D.frobenius p (k + k) A` whenever all simple roots pair evenly with `α_i^∨`
(`weylFrobenius_comp_weylFrobenius_of_forall_even`, and in rank one
`weylFrobenius_comp_weylFrobenius_of_rank_eq_one`).

## References

* R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, Mem. Amer. Math. Soc. **80** (1968),
  §§10–11; G. Malle & D. Testerman, *Linear Algebraic Groups and Finite Groups of Lie Type*,
  Cambridge Univ. Press (2011), §21.1 and Example 22.3.
-/

public section

open Multiplicative
namespace TauCeti.DynkinType.ChevalleyDatum
noncomputable section
universe v v'
variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ## Simple Weyl conjugation as a standard non-based endomorphism -/

section WeylConj
variable (i : Fin t.rank) (A : Type v) [CommRing A]

/-- Conjugation by a pinned simple Weyl representative is standard over every commutative ring. -/
@[simp] theorem isStandard_conj_weylElement : D.IsStandard
    (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1) : D.points A →* D.points A) :=
  (D.isStandard_def _).mpr ⟨⟨D.simpleReflectionCharacterMap i,
      D.simpleReflectionCharacterMap_injective i, D.isCharacterMap_conj_weylElement i A⟩,
    fun γ => ⟨_, D.map_range_rootSubgroupPoints_conj_weylElement i A γ⟩⟩

/-- Over any nontrivial commutative ring, simple Weyl conjugation is not based. -/
@[simp] theorem not_isBased_conj_weylElement [Nontrivial A] : ¬ D.IsBased
    (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1) : D.points A →* D.points A) :=
  fun hBased => let ⟨b, hb⟩ := D.exists_weylElement_conj_notMem_borelSubgroup A i
    hb (hBased.map_borelSubgroup_le
      ⟨b.val, b.property, by rw [MonoidHom.coe_ofClass, MulAut.conj_apply]⟩)

section Field
variable {D} {K : Type v} [Field K] [Infinite K]

/-- The character map of simple Weyl conjugation is `D.simpleReflectionCharacterMap i`. -/
@[simp] theorem IsStandard.characterMap_conj_weylElement :
    (D.isStandard_conj_weylElement i K).characterMap = D.simpleReflectionCharacterMap i :=
  (D.isStandard_conj_weylElement i K).characterMap_eq_of_isCharacterMap
    (D.isCharacterMap_conj_weylElement i K)

/-- The root permutation of simple Weyl conjugation is the simple reflection `s_i`. -/
@[simp] theorem IsStandard.rootPerm_conj_weylElement :
    (D.isStandard_conj_weylElement i K).rootPerm =
      (t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) :=
  Equiv.ext fun γ => (D.isStandard_conj_weylElement i K).rootPerm_eq_of_map_range
    (D.map_range_rootSubgroupPoints_conj_weylElement i K γ)

private theorem IsStandard.conj_weylElement_invariants [RootableBy Kˣ ℕ] (γ : Fin t.numRoots) :
    Units.map (Int.castRingHom K).toMonoidHom
        (t.chevalleyWeylSign ht (t.simpleIndex ht i) γ) =
      (D.isStandard_conj_weylElement i K).rootUnit γ ∧
      RingHom.id K = (D.isStandard_conj_weylElement i K).fieldEnd γ :=
  ((D.isStandard_conj_weylElement i K).eq_of_map_rootSubgroupPoints
    (β := (t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ)
    (c := Units.map (Int.castRingHom K).toMonoidHom
      (t.chevalleyWeylSign ht (t.simpleIndex ht i) γ))
    (g := RingHom.id K) fun u => by simp [D.weylElement_conj_rootSubgroupPoints]).2

/-- The scaling unit of simple Weyl conjugation on the `γ`-root subgroup is the Weyl sign. -/
@[simp] theorem IsStandard.rootUnit_conj_weylElement [RootableBy Kˣ ℕ] (γ : Fin t.numRoots) :
    (D.isStandard_conj_weylElement i K).rootUnit γ =
      Units.map (Int.castRingHom K).toMonoidHom
        (t.chevalleyWeylSign ht (t.simpleIndex ht i) γ) :=
  (IsStandard.conj_weylElement_invariants i γ).1.symm

/-- The field endomorphism of simple Weyl conjugation is `RingHom.id K`. -/
@[simp] theorem IsStandard.fieldEnd_conj_weylElement [RootableBy Kˣ ℕ] (γ : Fin t.numRoots) :
    (D.isStandard_conj_weylElement i K).fieldEnd γ = RingHom.id K :=
  (IsStandard.conj_weylElement_invariants i γ).2.symm

end Field

end WeylConj

/-! ## Weyl-twisted Frobenius endomorphisms -/

section WeylFrobenius
variable (i : Fin t.rank) (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- **The Weyl-twisted Frobenius endomorphism `Int(n_i(1)) ∘ Frob_{p^k}` on `D.points A`.** -/
def weylFrobenius : D.points A →* D.points A :=
  (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1) : D.points A →* D.points A).comp
    (D.frobenius p k A)

/-- Composite definition of `D.weylFrobenius i p k A`. -/
theorem weylFrobenius_def : D.weylFrobenius i p k A =
    (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1) : D.points A →* D.points A).comp
      (D.frobenius p k A) := (rfl)

/-- Pointwise formula for `D.weylFrobenius i p k A`. -/
theorem weylFrobenius_apply (g : D.points A) : D.weylFrobenius i p k A g =
    D.weylElement (t.simpleIndex ht i) A 1 * D.frobenius p k A g *
      (D.weylElement (t.simpleIndex ht i) A 1)⁻¹ := by simp [weylFrobenius_def, MulAut.conj_apply]

/-- At exponent `0`, `D.weylFrobenius` reduces to simple Weyl conjugation. -/
@[simp] theorem weylFrobenius_zero : D.weylFrobenius i p 0 A =
    (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1) : D.points A →* D.points A) := by
  rw [weylFrobenius_def, D.frobenius_zero, MonoidHom.comp_id]

/-- Underlying-matrix formula for `D.weylFrobenius i p k A`. -/
@[simp] theorem coe_weylFrobenius (g : D.points A) :
    (D.weylFrobenius i p k A g : Matrix.GeneralLinearGroup (Fin D.dim) A) =
      (D.weylElement (t.simpleIndex ht i) A 1 : Matrix.GeneralLinearGroup (Fin D.dim) A) *
        Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g *
        (D.weylElement (t.simpleIndex ht i) A 1 : Matrix.GeneralLinearGroup (Fin D.dim) A)⁻¹ := by
  rw [weylFrobenius_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_frobenius]

/-- `D.weylFrobenius` commutes with ring homomorphisms of the same exponential characteristic. -/
theorem map_weylFrobenius {B : Type v'} [CommRing B] [ExpChar B p] (f : A →+* B) (g : D.points A) :
    (D.pointsPresentation A).map (D.pointsPresentation B) f (D.weylFrobenius i p k A g) =
      D.weylFrobenius i p k B ((D.pointsPresentation A).map (D.pointsPresentation B) f g) := by
  have hw : (D.pointsPresentation A).map (D.pointsPresentation B) f
      (D.weylElement (t.simpleIndex ht i) A 1) = D.weylElement (t.simpleIndex ht i) B 1 :=
    Subtype.ext (by simp [GeneralLinear.IntegralPointsPresentation.coe_map, D.map_weylElement])
  rw [weylFrobenius_apply, weylFrobenius_apply, map_mul, map_mul, map_inv, D.map_frobenius, hw]

/-- On `D.torusPoints A`, `D.weylFrobenius` raises parameters to `p ^ k` and applies `s_i`. -/
@[simp] theorem weylFrobenius_torusPoints (s : Fin t.rank → Aˣ) :
    D.weylFrobenius i p k A (D.torusPoints A s) =
      D.torusPoints A (D.simpleReflectionTorusParameter i A (s ^ p ^ k)) := by
  rw [weylFrobenius_apply, D.frobenius_torusPoints, D.weylElement_conj_torusPoints]

/-- On `γ`-root points, `D.weylFrobenius` raises parameters to `p ^ k` and reflects by `s_i`. -/
@[simp] theorem weylFrobenius_rootSubgroupPoints (γ : Fin t.numRoots) (u : A) :
    D.weylFrobenius i p k A (D.rootSubgroupPoints γ A (ofAdd u)) = D.rootSubgroupPoints
      ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ) A
      (ofAdd (((t.chevalleyWeylSign ht (t.simpleIndex ht i) γ : ℤ) : A) * u ^ p ^ k)) := by
  rw [weylFrobenius_apply, D.frobenius_rootSubgroupPoints, D.weylElement_conj_rootSubgroupPoints]

/-- **Character map of `D.weylFrobenius`**: `(p ^ k : ℕ) • D.simpleReflectionCharacterMap i`. -/
theorem isCharacterMap_weylFrobenius : IsCharacterMap (D.torusPoints A) (D.weylFrobenius i p k A)
    ((p ^ k : ℕ) • D.simpleReflectionCharacterMap i) := by
  simpa only [weylFrobenius_def, smul_mul_assoc, one_mul] using
    (D.isCharacterMap_conj_weylElement i A).comp (D.isCharacterMap_frobenius p k A)

/-- **In rank one, the character map of `D.weylFrobenius i p k A` is `-((p ^ k : ℕ) • 1)`.** -/
theorem isCharacterMap_weylFrobenius_of_rank_eq_one (hr : t.rank = 1) :
    IsCharacterMap (D.torusPoints A) (D.weylFrobenius i p k A) (-((p ^ k : ℕ) • 1)) := by
  simpa only [D.simpleReflectionCharacterMap_eq_neg_one_of_rank_eq_one hr i, smul_neg] using
    D.isCharacterMap_weylFrobenius i p k A

/-- Over a perfect ring `A`, `D.weylFrobenius` maps the `γ`-root subgroup onto `s_i(γ)`. -/
@[simp] theorem map_range_rootSubgroupPoints_weylFrobenius [PerfectRing A p] (γ : Fin t.numRoots) :
    (D.rootSubgroupPoints γ A).range.map (D.weylFrobenius i p k A) = (D.rootSubgroupPoints
      ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ) A).range := by
  rw [weylFrobenius_def, ← Subgroup.map_map, D.map_range_rootSubgroupPoints_frobenius p k A γ,
    D.map_range_rootSubgroupPoints_conj_weylElement]

/-- **Over any perfect ring of exponential characteristic `p`, `D.weylFrobenius` is standard.** -/
@[simp] theorem isStandard_weylFrobenius [PerfectRing A p] :
    D.IsStandard (D.weylFrobenius i p k A) :=
  (D.isStandard_conj_weylElement i A).comp (D.isStandard_frobenius p k)

section Field
variable {D} {K : Type v} [Field K] [Infinite K] [ExpChar K p] [PerfectRing K p]

/-- The character map of `D.weylFrobenius i p k K` is
`(p ^ k : ℕ) • D.simpleReflectionCharacterMap i`. -/
@[simp] theorem IsStandard.characterMap_weylFrobenius :
    (D.isStandard_weylFrobenius i p k K).characterMap =
      (p ^ k : ℕ) • D.simpleReflectionCharacterMap i :=
  (D.isStandard_weylFrobenius i p k K).characterMap_eq_of_isCharacterMap
    (D.isCharacterMap_weylFrobenius i p k K)

/-- The root permutation of `D.weylFrobenius i p k K` is the simple reflection `s_i`. -/
@[simp] theorem IsStandard.rootPerm_weylFrobenius :
    (D.isStandard_weylFrobenius i p k K).rootPerm =
      (t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) :=
  Equiv.ext fun γ => (D.isStandard_weylFrobenius i p k K).rootPerm_eq_of_map_range
    (D.map_range_rootSubgroupPoints_weylFrobenius i p k K γ)

private theorem IsStandard.weylFrobenius_invariants [RootableBy Kˣ ℕ] (γ : Fin t.numRoots) :
    Units.map (Int.castRingHom K).toMonoidHom
        (t.chevalleyWeylSign ht (t.simpleIndex ht i) γ) =
      (D.isStandard_weylFrobenius i p k K).rootUnit γ ∧
      iterateFrobenius K p k = (D.isStandard_weylFrobenius i p k K).fieldEnd γ :=
  ((D.isStandard_weylFrobenius i p k K).eq_of_map_rootSubgroupPoints
    (β := (t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ)
    (c := Units.map (Int.castRingHom K).toMonoidHom
      (t.chevalleyWeylSign ht (t.simpleIndex ht i) γ))
    (g := iterateFrobenius K p k) fun u => by simp [iterateFrobenius_def]).2

/-- The scaling unit of `D.weylFrobenius i p k K` on the `γ`-root subgroup is the Weyl sign. -/
@[simp] theorem IsStandard.rootUnit_weylFrobenius [RootableBy Kˣ ℕ] (γ : Fin t.numRoots) :
    (D.isStandard_weylFrobenius i p k K).rootUnit γ =
      Units.map (Int.castRingHom K).toMonoidHom
        (t.chevalleyWeylSign ht (t.simpleIndex ht i) γ) :=
  (IsStandard.weylFrobenius_invariants i p k γ).1.symm

/-- The field endomorphism of `D.weylFrobenius i p k K` is `iterateFrobenius K p k`. -/
@[simp] theorem IsStandard.fieldEnd_weylFrobenius [RootableBy Kˣ ℕ] (γ : Fin t.numRoots) :
    (D.isStandard_weylFrobenius i p k K).fieldEnd γ = iterateFrobenius K p k :=
  (IsStandard.weylFrobenius_invariants i p k γ).2.symm

end Field

/-- **Over any nontrivial ring, `D.weylFrobenius` does not preserve `D.borelSubgroup A`.** -/
theorem not_map_borelSubgroup_weylFrobenius_le [Nontrivial A] :
    ¬ (D.borelSubgroup A).map (D.weylFrobenius i p k A) ≤ D.borelSubgroup A := fun hle => by
  have himg : D.weylFrobenius i p k A (D.rootSubgroupPoints (t.simpleIndex ht i) A (ofAdd 1)) ∈
      D.borelSubgroup A := hle ⟨_, D.positivePoints_le_borelSubgroup A
    (D.rootSubgroupPoints_mem_positivePoints A (support_subset_posRoots _ _
      (t.simpleIndex_mem_support i)) (ofAdd 1)), rfl⟩
  rw [weylFrobenius_apply, D.frobenius_rootSubgroupPoints, one_pow,
    D.weylElement_conj_rootSubgroupPoints_simpleIndex_mem_borelSubgroup_iff] at himg
  exact D.rootSubgroupPoints_ofAdd_one_ne_one A (t.simpleIndex ht i) himg

/-- **Over any nontrivial commutative ring, `D.weylFrobenius` is not based.** -/
@[simp] theorem not_isBased_weylFrobenius [Nontrivial A] : ¬ D.IsBased (D.weylFrobenius i p k A) :=
  fun h => D.not_map_borelSubgroup_weylFrobenius_le i p k A h.map_borelSubgroup_le

/-- **Square of `D.weylFrobenius` in general rank**: `Int(α_i^∨(-1)) ∘ D.frobenius p (k + k) A`. -/
theorem weylFrobenius_comp_weylFrobenius :
    (D.weylFrobenius i p k A).comp (D.weylFrobenius i p k A) =
      (MulAut.conj (D.simpleCorootPoints i A (-1)) : D.points A →* D.points A).comp
        (D.frobenius p (k + k) A) := MonoidHom.ext fun g => by
  simp only [MonoidHom.comp_apply, weylFrobenius_apply, map_mul, map_inv,
    D.frobenius_weylElement, one_pow, MonoidHom.coe_ofClass, MulAut.conj_apply]
  rw [D.frobenius_add, MonoidHom.comp_apply, ← D.weylElement_mul_self i A]; group

/-- **When every simple root pairs evenly with `α_i^∨`, `(weylFrobenius)² = frobenius(2k)`.** -/
theorem weylFrobenius_comp_weylFrobenius_of_forall_even
    (heven : ∀ m : Fin t.rank, Even ((t.simplyConnectedRootDatum ht).root (t.simpleIndex ht m) i)) :
    (D.weylFrobenius i p k A).comp (D.weylFrobenius i p k A) = D.frobenius p (k + k) A :=
  MonoidHom.ext fun g => by
    rw [D.weylFrobenius_comp_weylFrobenius, MonoidHom.comp_apply, MonoidHom.coe_ofClass,
      MulAut.conj_apply]; exact D.simpleCorootPoints_neg_one_conj_eq_self i heven A _

/-- Pointwise form of `weylFrobenius_comp_weylFrobenius_of_forall_even`. -/
theorem weylFrobenius_weylFrobenius_eq_frobenius_of_forall_even
    (heven : ∀ m : Fin t.rank, Even ((t.simplyConnectedRootDatum ht).root (t.simpleIndex ht m) i))
    (g : D.points A) : D.weylFrobenius i p k A (D.weylFrobenius i p k A g) =
      D.frobenius p (k + k) A g :=
  DFunLike.congr_fun (D.weylFrobenius_comp_weylFrobenius_of_forall_even i p k A heven) g

/-- **In rank one, `(D.weylFrobenius i p k A)² = D.frobenius p (k + k) A` on `D.points A`.** -/
theorem weylFrobenius_comp_weylFrobenius_of_rank_eq_one (hr : t.rank = 1) :
    (D.weylFrobenius i p k A).comp (D.weylFrobenius i p k A) = D.frobenius p (k + k) A :=
  D.weylFrobenius_comp_weylFrobenius_of_forall_even i p k A fun m => by
    obtain rfl : m = i := Fin.ext (by omega); simp

/-- Pointwise form of `weylFrobenius_comp_weylFrobenius_of_rank_eq_one`. -/
theorem weylFrobenius_weylFrobenius_eq_frobenius_of_rank_eq_one (hr : t.rank = 1) (g : D.points A) :
    D.weylFrobenius i p k A (D.weylFrobenius i p k A g) = D.frobenius p (k + k) A g :=
  DFunLike.congr_fun (D.weylFrobenius_comp_weylFrobenius_of_rank_eq_one i p k A hr) g

end WeylFrobenius
end
end TauCeti.DynkinType.ChevalleyDatum
