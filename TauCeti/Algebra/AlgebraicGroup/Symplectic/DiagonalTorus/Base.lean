/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.RootDatum
public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic

/-!
# A base of the root datum of the symplectic group

For `Sp₂ₘ` with its paired diagonal torus, the roots

```text
α_i = e_i - e_(i+1),  0 ≤ i < m - 1,      α_(m-1) = 2 e_(m-1)
```

form a base of `TauCeti.Symplectic.diagonalRootDatum`. Every root `e_a - e_b` with `a < b`
telescopes into consecutive differences, and every root `e_a + e_b`, including the long root
`2 e_a`, is `(e_a - e_(m-1)) + (e_b - e_(m-1)) + 2 e_(m-1)`; the coroots decompose in the same way
over the simple coroots `e_i - e_(i+1)` and `e_(m-1)`. Partial coordinate sums detect the simple
roots and coroots, which proves their linear independence.

The resulting Cartan matrix is `CartanMatrix.C m`. The positive roots are exactly the positive
long roots `2 e_i`, the positive sums `e_i + e_j`, and the differences `e_i - e_j` with `i < j`.

The base equips the diagonal root datum with its simple and positive roots. This is what allows it
to be compared with the pinned type-`C` root datum up to a labelling of the simple roots, and what
supplies the positive roots underlying a Borel subgroup and the Bruhat theory of `Sp₂ₘ`.

## Main declarations

* `TauCeti.Symplectic.diagonalSimpleRootIndex`: the root subgroup of the `i`-th simple root.
* `TauCeti.Symplectic.diagonalRootBase`: the Bourbaki-numbered base of the diagonal root datum.
* `TauCeti.Symplectic.mem_diagonalRootBase_support`: its support consists of the simple indices.
* `TauCeti.Symplectic.hasCartanType_diagonalRootDatum`: this base has Cartan type `Cₘ`.
* `TauCeti.Symplectic.diagonalRootBase_isPos_positiveLong` and its companions: the positive roots
  of this base.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 12.1.

The organization follows `TauCeti.GeneralLinear.diagonalRootBase` for the diagonal torus of
`GL_(n+1)`.
-/

public section

open Function Set

namespace TauCeti.Symplectic

open GLSymplecticFin

universe u

variable {m : ℕ}

/-! ### The simple root indices -/

/-- The root subgroup of the `i`-th simple root of `Sp₂ₘ` in Bourbaki numbering: the difference
root `e_i - e_(i+1)` before the last node, and the long root `2 e_(m-1)` at the last node. -/
def diagonalSimpleRootIndex (m : ℕ) (i : Fin m) : RootSubgroupIndex m :=
  if h : (i : ℕ) + 1 < m then .difference i ⟨i + 1, h⟩ (by simp [Fin.ext_iff])
  else .positiveLong i

/-- Before the last node, the simple root is the difference root `e_i - e_(i+1)`. -/
theorem diagonalSimpleRootIndex_of_lt (i : Fin m) (h : (i : ℕ) + 1 < m) :
    diagonalSimpleRootIndex m i = .difference i ⟨i + 1, h⟩ (by simp [Fin.ext_iff]) := by
  simp [diagonalSimpleRootIndex, h]

/-- At the last node, the simple root is the long root `2 e_(m-1)`. -/
theorem diagonalSimpleRootIndex_of_not_lt (i : Fin m) (h : ¬(i : ℕ) + 1 < m) :
    diagonalSimpleRootIndex m i = .positiveLong i := by
  simp [diagonalSimpleRootIndex, h]

/-- Distinct nodes have distinct simple roots. -/
theorem diagonalSimpleRootIndex_injective (m : ℕ) : Injective (diagonalSimpleRootIndex m) := by
  intro i j hij
  by_cases hi : (i : ℕ) + 1 < m <;> by_cases hj : (j : ℕ) + 1 < m <;>
    simp_all [diagonalSimpleRootIndex_of_lt, diagonalSimpleRootIndex_of_not_lt]

/-- The support formed by the simple root indices. -/
private abbrev diagonalSimpleSupport (m : ℕ) : Finset (RootSubgroupIndex m) :=
  simpleSupport (diagonalSimpleRootIndex_injective m)

private lemma diagonalSimpleRootIndex_mem (i : Fin m) :
    diagonalSimpleRootIndex m i ∈ (diagonalSimpleSupport m : Set (RootSubgroupIndex m)) :=
  (mem_simpleSupport _).2 ⟨i, rfl⟩

/-- The character `e_a` of the diagonal torus. -/
private noncomputable abbrev character (a : Fin m) : ULift.{u} (Fin m) →₀ ℤ :=
  Finsupp.single (ULift.up a) 1

/-- The cocharacter `e_a` of the diagonal torus. -/
private abbrev cocharacter (a : Fin m) : ULift.{u} (Fin m) → ℤ :=
  Pi.single (ULift.up a) 1

private lemma character_sub_mem {a b : Fin m} (hab : a ≤ b) :
    character.{u} a - character b ∈ AddSubmonoid.closure
      ((diagonalRootDatum.{u} m).root '' (diagonalSimpleSupport m : Set _)) := by
  refine sub_mem_of_consecutive_sub_mem_fin _ _ (fun a b h => AddSubmonoid.subset_closure ?_) hab
  refine ⟨_, diagonalSimpleRootIndex_mem a, ?_⟩
  have ha : (a : ℕ) + 1 < m := h ▸ b.isLt
  have hb : (⟨a + 1, ha⟩ : Fin m) = b := Fin.ext h
  subst hb
  rw [diagonalSimpleRootIndex_of_lt a ha, diagonalRootDatum_root_difference]

private lemma character_add_mem (a b : Fin m) :
    character.{u} a + character b ∈ AddSubmonoid.closure
      ((diagonalRootDatum.{u} m).root '' (diagonalSimpleSupport m : Set _)) := by
  refine add_mem_of_consecutive_sub_mem_fin _ _ (fun a b h => ?_) (fun c hc => ?_) a b
  · exact character_sub_mem (Fin.le_def.2 (by omega))
  · refine AddSubmonoid.subset_closure ⟨_, diagonalSimpleRootIndex_mem c, ?_⟩
    rw [diagonalSimpleRootIndex_of_not_lt c (by omega), diagonalRootDatum_root_positiveLong,
      ← Finsupp.single_add, one_add_one_eq_two]

private lemma cocharacter_sub_mem {a b : Fin m} (hab : a ≤ b) :
    cocharacter.{u} a - cocharacter b ∈ AddSubmonoid.closure
      ((diagonalRootDatum.{u} m).coroot '' (diagonalSimpleSupport m : Set _)) := by
  refine sub_mem_of_consecutive_sub_mem_fin _ _ (fun a b h => AddSubmonoid.subset_closure ?_) hab
  refine ⟨_, diagonalSimpleRootIndex_mem a, ?_⟩
  have ha : (a : ℕ) + 1 < m := h ▸ b.isLt
  have hb : (⟨a + 1, ha⟩ : Fin m) = b := Fin.ext h
  subst hb
  rw [diagonalSimpleRootIndex_of_lt a ha, diagonalRootDatum_coroot_difference]

private lemma cocharacter_mem (a : Fin m) :
    cocharacter.{u} a ∈ AddSubmonoid.closure
      ((diagonalRootDatum.{u} m).coroot '' (diagonalSimpleSupport m : Set _)) := by
  let c : Fin m := ⟨m - 1, by have := a.isLt; omega⟩
  have hc : cocharacter.{u} c ∈ AddSubmonoid.closure
      ((diagonalRootDatum.{u} m).coroot '' (diagonalSimpleSupport m : Set _)) := by
    refine AddSubmonoid.subset_closure ⟨_, diagonalSimpleRootIndex_mem c, ?_⟩
    rw [diagonalSimpleRootIndex_of_not_lt c (by simp [c]; omega),
      diagonalRootDatum_coroot_positiveLong]
  rw [← sub_add_cancel (cocharacter.{u} a) (cocharacter c)]
  exact AddSubmonoid.add_mem _ (cocharacter_sub_mem (Fin.le_def.2 (by simp [c]; omega))) hc

private lemma cocharacter_add_mem (a b : Fin m) :
    cocharacter.{u} a + cocharacter b ∈ AddSubmonoid.closure
      ((diagonalRootDatum.{u} m).coroot '' (diagonalSimpleSupport m : Set _)) :=
  AddSubmonoid.add_mem _ (cocharacter_mem a) (cocharacter_mem b)

/-! ### Linear independence of the simple roots and coroots -/

/-- The partial coordinate sums `y ↦ (∑_(a ≤ j) y a)_j`, which detect the simple coroots. -/
private noncomputable def partialSum (m : ℕ) : (ULift.{u} (Fin m) → ℤ) →ₗ[ℤ] (Fin m → ℤ) :=
  LinearMap.pi fun j => ∑ a ∈ Finset.Iic j, LinearMap.proj (ULift.up a)

private lemma partialSum_cocharacter (a j : Fin m) :
    partialSum.{u} m (cocharacter a) j = if a ≤ j then 1 else 0 := by
  simp [partialSum, Pi.single_apply]

/-- The coefficient of the `i`-th simple root under the partial coordinate sums: `2` at the long
simple root and `1` otherwise. -/
private def simpleCoefficient (i : Fin m) : ℤ := if (i : ℕ) + 1 < m then 1 else 2

private lemma partialSum_coe_root_diagonalSimpleRootIndex (i : Fin m) :
    partialSum.{u} m ⇑((diagonalRootDatum.{u} m).root (diagonalSimpleRootIndex m i)) =
      Pi.single i (simpleCoefficient i) := by
  funext j
  by_cases h : (i : ℕ) + 1 < m
  · rw [diagonalSimpleRootIndex_of_lt i h, diagonalRootDatum_root_difference]
    simp only [Finsupp.coe_sub, Finsupp.single_eq_pi_single, map_sub, Pi.sub_apply]
    rw [partialSum_cocharacter, partialSum_cocharacter]
    simp only [simpleCoefficient, h, ↓reduceIte, Pi.single_apply, Fin.le_def, Fin.ext_iff]
    split_ifs <;> omega
  · rw [diagonalSimpleRootIndex_of_not_lt i h, diagonalRootDatum_root_positiveLong]
    have h2 : (Finsupp.single (ULift.up i) (2 : ℤ) : ULift.{u} (Fin m) → ℤ) =
        cocharacter i + cocharacter i := by
      rw [Finsupp.single_eq_pi_single, ← Pi.single_add, one_add_one_eq_two]
    rw [h2, map_add, Pi.add_apply, partialSum_cocharacter]
    simp only [simpleCoefficient, h, ↓reduceIte, Pi.single_apply, Fin.le_def, Fin.ext_iff]
    have := j.isLt
    split_ifs <;> omega

private lemma partialSum_coroot_diagonalSimpleRootIndex (i : Fin m) :
    partialSum.{u} m ((diagonalRootDatum.{u} m).coroot (diagonalSimpleRootIndex m i)) =
      Pi.single i 1 := by
  funext j
  by_cases h : (i : ℕ) + 1 < m
  · rw [diagonalSimpleRootIndex_of_lt i h, diagonalRootDatum_coroot_difference, map_sub,
      Pi.sub_apply, partialSum_cocharacter, partialSum_cocharacter]
    simp only [Pi.single_apply, Fin.le_def, Fin.ext_iff]
    split_ifs <;> omega
  · rw [diagonalSimpleRootIndex_of_not_lt i h, diagonalRootDatum_coroot_positiveLong,
      partialSum_cocharacter]
    simp only [Pi.single_apply, Fin.le_def, Fin.ext_iff]
    have := j.isLt
    split_ifs <;> omega

private lemma linearIndependent_root_diagonalSimpleRootIndex (m : ℕ) :
    LinearIndependent ℤ
      ((diagonalRootDatum.{u} m).root ∘ diagonalSimpleRootIndex m) := by
  refine LinearIndependent.of_comp ((partialSum.{u} m).comp Finsupp.lcoeFun) ?_
  have h : ((partialSum.{u} m).comp Finsupp.lcoeFun) ∘
      ((diagonalRootDatum.{u} m).root ∘ diagonalSimpleRootIndex m) =
      fun i => Pi.single i (simpleCoefficient i) :=
    funext partialSum_coe_root_diagonalSimpleRootIndex
  rw [h]
  exact Pi.linearIndependent_single_of_ne_zero fun i => by
    unfold simpleCoefficient
    split_ifs <;> norm_num

private lemma linearIndependent_coroot_diagonalSimpleRootIndex (m : ℕ) :
    LinearIndependent ℤ
      ((diagonalRootDatum.{u} m).coroot ∘ diagonalSimpleRootIndex m) := by
  refine LinearIndependent.of_comp (partialSum.{u} m) ?_
  have h : partialSum.{u} m ∘ ((diagonalRootDatum.{u} m).coroot ∘ diagonalSimpleRootIndex m) =
      fun i => Pi.single i 1 :=
    funext partialSum_coroot_diagonalSimpleRootIndex
  rw [h]
  exact Pi.linearIndependent_single_one (Fin m) ℤ

/-! ### The base -/

/-- The Bourbaki-numbered base of the root datum of `Sp₂ₘ` relative to its diagonal torus,
supported on the roots `e_i - e_(i+1)` for `i < m - 1` and `2 e_(m-1)`. -/
noncomputable def diagonalRootBase (m : ℕ) : (diagonalRootDatum.{u} m).Base where
  support := diagonalSimpleSupport m
  linearIndepOn_root :=
    linearIndepOn_simpleSupport _ _ (linearIndependent_root_diagonalSimpleRootIndex m)
  linearIndepOn_coroot :=
    linearIndepOn_simpleSupport _ _ (linearIndependent_coroot_diagonalSimpleRootIndex m)
  root_mem_or_neg_mem p := by
    cases p with
    | positiveLong i =>
        left
        rw [diagonalRootDatum_root_positiveLong, ← one_add_one_eq_two, Finsupp.single_add]
        exact character_add_mem i i
    | negativeLong i =>
        right
        rw [diagonalRootDatum_root_negativeLong, neg_neg, ← one_add_one_eq_two,
          Finsupp.single_add]
        exact character_add_mem i i
    | difference i j hij =>
        rw [diagonalRootDatum_root_difference]
        rcases lt_or_gt_of_ne hij with h | h
        · exact Or.inl (character_sub_mem h.le)
        · exact Or.inr (by rw [neg_sub]; exact character_sub_mem h.le)
    | positiveSum i j hij =>
        exact Or.inl (by rw [diagonalRootDatum_root_positiveSum]; exact character_add_mem i j)
    | negativeSum i j hij =>
        exact Or.inr (by
          rw [diagonalRootDatum_root_negativeSum, neg_neg]; exact character_add_mem i j)
  coroot_mem_or_neg_mem p := by
    cases p with
    | positiveLong i =>
        exact Or.inl (by rw [diagonalRootDatum_coroot_positiveLong]; exact cocharacter_mem i)
    | negativeLong i =>
        exact Or.inr (by
          rw [diagonalRootDatum_coroot_negativeLong, neg_neg]; exact cocharacter_mem i)
    | difference i j hij =>
        rw [diagonalRootDatum_coroot_difference]
        rcases lt_or_gt_of_ne hij with h | h
        · exact Or.inl (cocharacter_sub_mem h.le)
        · exact Or.inr (by rw [neg_sub]; exact cocharacter_sub_mem h.le)
    | positiveSum i j hij =>
        exact Or.inl (by
          rw [diagonalRootDatum_coroot_positiveSum]; exact cocharacter_add_mem i j)
    | negativeSum i j hij =>
        exact Or.inr (by
          rw [diagonalRootDatum_coroot_negativeSum, neg_neg]; exact cocharacter_add_mem i j)

/-- The support of the diagonal base is the image of the simple-root index map. -/
theorem diagonalRootBase_support (m : ℕ) :
    (diagonalRootBase.{u} m).support = simpleSupport (diagonalSimpleRootIndex_injective m) :=
  (rfl)

/-- A root index belongs to the diagonal base exactly when it is one of the simple indices. -/
@[simp]
theorem mem_diagonalRootBase_support (p : RootSubgroupIndex m) :
    p ∈ (diagonalRootBase.{u} m).support ↔ ∃ i, diagonalSimpleRootIndex m i = p := by
  rw [diagonalRootBase_support, mem_simpleSupport]

/-! ### The Cartan type -/

private lemma dotPairing_character (a : Fin m) (y : ULift.{u} (Fin m) → ℤ) :
    SplitTorus.dotPairing (character a) y = y (ULift.up a) := by
  simp [SplitTorus.dotPairing_apply]

/-- The pairings of the simple roots of the diagonal root datum are the entries of the type-`C`
Cartan matrix. -/
theorem diagonalRootDatum_pairing_diagonalSimpleRootIndex (i j : Fin m) :
    (diagonalRootDatum.{u} m).pairing (diagonalSimpleRootIndex m i)
        (diagonalSimpleRootIndex m j) =
      CartanMatrix.C m i j := by
  rw [← RootPairing.root_coroot_eq_pairing, diagonalRootDatum_toLinearMap]
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : (i : ℕ) + 1 < m <;> by_cases h' : (j : ℕ) + 1 < m
  on_goal 1 => rw [diagonalSimpleRootIndex_of_lt i h, diagonalSimpleRootIndex_of_lt j h',
      diagonalRootDatum_root_difference, diagonalRootDatum_coroot_difference]
  on_goal 2 => rw [diagonalSimpleRootIndex_of_lt i h, diagonalSimpleRootIndex_of_not_lt j h',
      diagonalRootDatum_root_difference, diagonalRootDatum_coroot_positiveLong]
  on_goal 3 => rw [diagonalSimpleRootIndex_of_not_lt i h, diagonalSimpleRootIndex_of_lt j h',
      diagonalRootDatum_root_positiveLong, diagonalRootDatum_coroot_difference,
      ← one_add_one_eq_two, Finsupp.single_add]
  on_goal 4 => rw [diagonalSimpleRootIndex_of_not_lt i h, diagonalSimpleRootIndex_of_not_lt j h',
      diagonalRootDatum_root_positiveLong, diagonalRootDatum_coroot_positiveLong,
      ← one_add_one_eq_two, Finsupp.single_add]
  all_goals
    simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, dotPairing_character,
      CartanMatrix.C, Matrix.of_apply, Pi.single_apply, ULift.up_inj, Fin.ext_iff]
    split_ifs <;> omega

/-- **The diagonal root datum of `Sp₂ₘ`, with its Bourbaki-numbered base, has Cartan type
`Cₘ`.** -/
theorem hasCartanType_diagonalRootDatum (m : ℕ) :
    HasCartanType (diagonalRootDatum.{u} m) (diagonalRootBase m) (.C m) :=
  hasCartanType_of_pairing_eq (diagonalSimpleRootIndex_injective m) rfl fun i j => by
    simpa [-diagonalRootDatum_pairing_apply] using
      diagonalRootDatum_pairing_diagonalSimpleRootIndex (m := m) i j

/-! ### The positive roots -/

private lemma isPos_of_root_mem {p : RootSubgroupIndex m}
    (h : (diagonalRootDatum.{u} m).root p ∈ AddSubmonoid.closure
      ((diagonalRootDatum.{u} m).root '' (diagonalSimpleSupport m : Set _))) :
    (diagonalRootBase.{u} m).IsPos p :=
  (mem_posRoots _ _ _).1 ((mem_posRoots_iff_root_mem_posRootCone _ _).2
    (by rwa [posRootCone_def]))

private lemma not_isPos_of_root_eq_neg {p q : RootSubgroupIndex m}
    (hq : (diagonalRootBase.{u} m).IsPos q)
    (h : (diagonalRootDatum.{u} m).root p = -(diagonalRootDatum.{u} m).root q) :
    ¬(diagonalRootBase.{u} m).IsPos p := by
  let _ := (diagonalRootDatum.{u} m).indexNeg
  have hp : p = -q := (diagonalRootDatum.{u} m).root.injective (by
    rw [h, RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self])
  rw [hp, RootPairing.Base.IsPos.neg_iff_not, not_not]
  exact hq

/-- The long root `2 eᵢ` is positive. -/
@[simp]
theorem diagonalRootBase_isPos_positiveLong (i : Fin m) :
    (diagonalRootBase.{u} m).IsPos (.positiveLong i) :=
  isPos_of_root_mem (by
    rw [diagonalRootDatum_root_positiveLong, ← one_add_one_eq_two, Finsupp.single_add]
    exact character_add_mem i i)

/-- The long root `-2 eᵢ` is not positive. -/
@[simp]
theorem not_diagonalRootBase_isPos_negativeLong (i : Fin m) :
    ¬(diagonalRootBase.{u} m).IsPos (.negativeLong i) :=
  not_isPos_of_root_eq_neg (diagonalRootBase_isPos_positiveLong i) (by
    rw [diagonalRootDatum_root_negativeLong, diagonalRootDatum_root_positiveLong])

/-- The sum root `eᵢ + eⱼ` is positive. -/
@[simp]
theorem diagonalRootBase_isPos_positiveSum {i j : Fin m} (hij : i < j) :
    (diagonalRootBase.{u} m).IsPos (.positiveSum i j hij) :=
  isPos_of_root_mem (by
    rw [diagonalRootDatum_root_positiveSum]
    exact character_add_mem i j)

/-- The sum root `-(eᵢ + eⱼ)` is not positive. -/
@[simp]
theorem not_diagonalRootBase_isPos_negativeSum {i j : Fin m} (hij : i < j) :
    ¬(diagonalRootBase.{u} m).IsPos (.negativeSum i j hij) :=
  not_isPos_of_root_eq_neg (diagonalRootBase_isPos_positiveSum hij) (by
    rw [diagonalRootDatum_root_negativeSum, diagonalRootDatum_root_positiveSum])

/-- The difference root `eᵢ - eⱼ` is positive exactly when `i < j`. -/
@[simp]
theorem diagonalRootBase_isPos_difference_iff {i j : Fin m} (hij : i ≠ j) :
    (diagonalRootBase.{u} m).IsPos (.difference i j hij) ↔ i < j := by
  rcases lt_or_gt_of_ne hij with h | h
  · refine iff_of_true (isPos_of_root_mem ?_) h
    rw [diagonalRootDatum_root_difference]
    exact character_sub_mem h.le
  · refine iff_of_false (not_isPos_of_root_eq_neg (q := .difference j i hij.symm)
      (isPos_of_root_mem ?_) ?_) (not_lt_of_gt h)
    · rw [diagonalRootDatum_root_difference]
      exact character_sub_mem h.le
    · rw [diagonalRootDatum_root_difference, diagonalRootDatum_root_difference, neg_sub]

end TauCeti.Symplectic
