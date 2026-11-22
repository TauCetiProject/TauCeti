/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.LinearCombination
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Frøyshov's reduced instanton homology

The instanton chain complex `C` of an integral homology sphere, with `d : Cᵢ → Cᵢ₋₁` and grading
in `ZMod 8`, carries three maps counting trajectories to and from the trivial connection and
the point class:

`δ : C₁ → R`,  `δ' : R → C₄`,  `ν : Cᵢ → Cᵢ₋₄`,

subject to `δ d = 0`, `d δ' = 0` and `d ν - ν d + 2 δ' δ = 0`. This file develops the homological
algebra Frøyshov extracts from these relations. The maps `δⱼ = δ νʲ` vanish on boundaries, so they
are maps on homology, and the elements `νʲ δ'(1)` are cycles, so they have homology classes `δ'ⱼ`.
The **reduced homology** is the subquotient

`Î = Z(I) / B(I)`,  `Z(I) = ⋂ⱼ ker δⱼ`,  `B(I) = Σⱼ R δ'ⱼ`

of the homology, and `ν` descends to a degree `-4` endomorphism `u` of `Î`. On a cycle `x` with
`δ x = 0` the extra term of the commutator vanishes, so `ν x` is a cycle; changing `x` by a boundary
`d y` changes `ν x` by the boundary `d (ν y)` plus `2 δ(y) δ'(1)`, which lies in `B(I)`.

The proofs only use the gradings through one fact: `δ νʲ δ'(1) = 0` for every `j`, since
`νʲ δ'(1)` lies in degree `4 - 4j`, which is `0` or `4`, never `1`. For the same reason `Z(I)` is
all of the homology outside degrees `1` and `5`, and `B(I)` vanishes outside degrees `0` and `4`.

The maps are recorded as families over all degrees that vanish off their degree, following
`Homotopy`, so that the relations are stated without transporting along equalities of degrees.
The coefficient ring is arbitrary: the integral counts, their localization away from `2` and their
complexification all fit.

## Main definitions and results

* `TauCeti.Instanton.ReducibleMaps`: the maps `δ`, `δ'` and `ν` with their relations.
* `TauCeti.Instanton.ReducibleMaps.homologyδ`: the map `δⱼ` on homology, computed on classes of
  cycles by `TauCeti.Instanton.ReducibleMaps.homologyδ_moduleCatKerHomologyClass`.
* `TauCeti.Instanton.ReducibleMaps.homologyδ'`: the class `δ'ⱼ` of the cycle `νʲ δ'(1)`.
* `TauCeti.Instanton.ReducibleMaps.reducedCycles`,
  `TauCeti.Instanton.ReducibleMaps.reducedBoundaries`: the submodules `Z(I)` and `B(I)` of the
  homology, with `TauCeti.Instanton.ReducibleMaps.reducedBoundaries_le_reducedCycles`.
* `TauCeti.Instanton.ReducibleMaps.comap_reducedBoundaries`: the cycles whose classes lie in `B(I)`
  are the sums of boundaries and combinations of the cycles `νʲ δ'(1)`.
* `TauCeti.Instanton.ReducibleMaps.reducedHomology`: the subquotient `Î = Z(I) / B(I)`.
* `TauCeti.Instanton.ReducibleMaps.reducedPointMap`: the endomorphism `u : Îᵢ → Îᵢ₋₄` induced by
  `ν`, computed on classes by `TauCeti.Instanton.ReducibleMaps.reducedPointMap_mk`.
* `TauCeti.Instanton.ReducibleMaps.reducedCycles_eq_top`,
  `TauCeti.Instanton.ReducibleMaps.reducedBoundaries_eq_bot`: the degrees where `Z(I)` and `B(I)`
  are trivial.

## References

* K. A. Frøyshov, *Equivariant aspects of Yang–Mills Floer theory*, Topology 41 (2002),
  Section 2 and Definition 1, in the dual cohomological convention.
* C. Scaduto, *Instantons and odd Khovanov homology*, J. Topology 8 (2015), Section 9.
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex

namespace TauCeti.Instanton

variable {R : Type*} [Ring R]

variable (C : ChainComplex (ModuleCat R) (ZMod 8)) in
/-- **Reducible maps** on a `ZMod 8`-graded chain complex `C` with `d : Cᵢ → Cᵢ₋₁`: the maps
`δ : C₁ → R`, `δ' : R → C₄`, given by the element `δ'(1)`, and `ν : Cᵢ → Cᵢ₋₄`, satisfying
`δ d = 0`, `d δ' = 0` and `d ν - ν d + 2 δ' δ = 0`. Each map is recorded as a family over all
degrees which vanishes off its degree, so that a structure is determined by `δ₁`, `δ'₄` and the
maps `Cᵢ → Cᵢ₋₄`. -/
@[ext]
structure ReducibleMaps where
  /-- The map `δ`, as a family vanishing outside degree `1`. -/
  δ (i : ZMod 8) : C.X i →ₗ[R] R
  /-- The element `δ'(1)`, as a family vanishing outside degree `4`. -/
  δ' (i : ZMod 8) : C.X i
  /-- The map `ν`, as a family `Cᵢ → Cⱼ` vanishing unless `j = i - 4`. -/
  ν (i j : ZMod 8) : C.X i →ₗ[R] C.X j
  δ_eq_zero (i : ZMod 8) (hi : i ≠ 1) : δ i = 0
  δ'_eq_zero (i : ZMod 8) (hi : i ≠ 4) : δ' i = 0
  ν_eq_zero (i j : ZMod 8) (hij : i ≠ j + 4) : ν i j = 0
  /-- `δ d = 0`. -/
  δ_comp_d (i j : ZMod 8) : δ j ∘ₗ (C.d i j).hom = 0
  /-- `d δ' = 0`. -/
  d_δ' (i j : ZMod 8) : (C.d i j).hom (δ' i) = 0
  /-- `d ν - ν d + 2 δ' δ = 0`, as maps `Cᵢ → Cⱼ`; only `j = i - 5` carries information. -/
  comm (i j : ZMod 8) : (C.d (j + 1) j).hom ∘ₗ ν i (j + 1) - ν (i - 1) j ∘ₗ (C.d i (i - 1)).hom +
    2 • (δ i).smulRight (δ' j) = 0

namespace ReducibleMaps

variable {C : ChainComplex (ModuleCat R) (ZMod 8)} (D : ReducibleMaps C)

/-- The relation `d ν - ν d + 2 δ' δ = 0` on an element, for any presentation of the degrees. -/
lemma d_ν_apply {i m n j : ZMod 8} (hm : m + 1 = i) (hn : j + 1 = n) (x : C.X i) :
    (C.d n j).hom (D.ν i n x) = D.ν m j ((C.d i m).hom x) - (2 * D.δ i x) • D.δ' j := by
  obtain rfl : m = i - 1 := eq_sub_of_add_eq hm
  subst hn
  have h := LinearMap.congr_fun (D.comm i j) x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.zero_apply] at h
  rw [two_nsmul] at h
  rw [mul_smul, two_smul, eq_sub_iff_add_eq, ← sub_eq_zero, ← h]
  abel

/-- The iterate `δ νᵏ : Cᵢ → R`, vanishing unless `i = 1 + 4 k`. -/
def δIter : ℕ → (i : ZMod 8) → C.X i →ₗ[R] R
  | 0, i => D.δ i
  | k + 1, i => δIter k (i - 4) ∘ₗ D.ν i (i - 4)

/-- The iterate `νᵏ δ'(1)`, an element of `Cᵢ` vanishing unless `i = 4 - 4 k`. -/
def δ'Iter : ℕ → (i : ZMod 8) → C.X i
  | 0, i => D.δ' i
  | k + 1, i => D.ν (i + 4) i (δ'Iter k (i + 4))

@[simp]
lemma δIter_zero (i : ZMod 8) : D.δIter 0 i = D.δ i := (rfl)

lemma δIter_succ (k : ℕ) (i : ZMod 8) :
    D.δIter (k + 1) i = D.δIter k (i - 4) ∘ₗ D.ν i (i - 4) := (rfl)

@[simp]
lemma δ'Iter_zero (i : ZMod 8) : D.δ'Iter 0 i = D.δ' i := (rfl)

/-- `νᵏ⁺¹ δ'(1) = ν (νᵏ δ'(1))`, for any presentation of the degrees. -/
lemma δ'Iter_succ (k : ℕ) {i j : ZMod 8} (h : j + 4 = i) :
    D.δ'Iter (k + 1) j = D.ν i j (D.δ'Iter k i) := by
  subst h
  exact (rfl)

/-- The multiples of `4` in `ZMod 8` are `0` and `4`. -/
private lemma four_mul_natCast (k : ℕ) : (4 * k : ZMod 8) = 0 ∨ (4 * k : ZMod 8) = 4 := by
  have h8 : (8 : ZMod 8) = 0 := rfl
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · left
    push_cast
    linear_combination (m : ZMod 8) * h8
  · right
    push_cast
    linear_combination (m : ZMod 8) * h8

lemma δIter_eq_zero (k : ℕ) {i : ZMod 8} (hi : i ≠ 1 + 4 * k) : D.δIter k i = 0 := by
  induction k generalizing i with
  | zero => exact D.δ_eq_zero i (by simpa using hi)
  | succ k ih =>
    rw [δIter_succ, ih fun h ↦ hi (by push_cast; linear_combination h), LinearMap.zero_comp]

lemma δ'Iter_eq_zero (k : ℕ) {i : ZMod 8} (hi : i + 4 * k ≠ 4) : D.δ'Iter k i = 0 := by
  induction k generalizing i with
  | zero => exact D.δ'_eq_zero i (by simpa using hi)
  | succ k ih =>
    rw [D.δ'Iter_succ k rfl, ih fun h ↦ hi (by push_cast; linear_combination h), map_zero]

/-- `δ νʲ νᵏ δ'(1) = 0`: the element `νᵏ δ'(1)` lies in degree `0` or `4`, where every `δ νʲ`
vanishes. -/
@[simp]
lemma δIter_δ'Iter (j k : ℕ) (i : ZMod 8) : D.δIter j i (D.δ'Iter k i) = 0 := by
  by_cases hi : i = 1 + 4 * j
  · rw [D.δ'Iter_eq_zero k, map_zero]
    subst hi
    intro h'
    rcases four_mul_natCast (j + k) with h | h <;> push_cast at h
    · have h3 : (3 : ZMod 8) = 0 := by linear_combination h - h'
      exact absurd h3 (by decide)
    · have h1 : (1 : ZMod 8) = 0 := by linear_combination h' - h
      exact absurd h1 (by decide)
  · rw [D.δIter_eq_zero j hi, LinearMap.zero_apply]

@[simp]
lemma δIter_δ' (k : ℕ) (i : ZMod 8) : D.δIter k i (D.δ' i) = 0 :=
  D.δIter_δ'Iter k 0 i

/-- `δ νᵏ d = 0`. -/
@[simp]
lemma δIter_d (k : ℕ) (i j : ZMod 8) (x : C.X i) : D.δIter k j ((C.d i j).hom x) = 0 := by
  induction k generalizing i j x with
  | zero => exact LinearMap.congr_fun (D.δ_comp_d i j) x
  | succ k ih =>
    by_cases hij : j + 1 = i
    · subst hij
      have h := D.d_ν_apply (m := j) (n := j - 4 + 1) (j := j - 4) rfl rfl x
      rw [eq_sub_iff_add_eq] at h
      rw [δIter_succ, LinearMap.comp_apply, ← h, map_add, map_smul, ih, δIter_δ', smul_zero,
        add_zero]
    · rw [C.shape i j (by simpa using hij), ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]

/-- `d νᵏ δ'(1) = 0`: the elements `νᵏ δ'(1)` are cycles. -/
@[simp]
lemma d_δ'Iter (k : ℕ) (i j : ZMod 8) : (C.d i j).hom (D.δ'Iter k i) = 0 := by
  induction k generalizing i j with
  | zero => exact D.d_δ' i j
  | succ k ih =>
    by_cases hij : j + 1 = i
    · rw [D.δ'Iter_succ k rfl, D.d_ν_apply (m := i + 3) (by ring) hij, ih, map_zero,
        ← δIter_zero, δIter_δ'Iter, mul_zero, zero_smul, sub_zero]
    · rw [C.shape i j (by simpa using hij), ModuleCat.hom_zero, LinearMap.zero_apply]

/-! ### The maps `δⱼ` on homology and the classes `δ'ⱼ` -/

/-- The map `δⱼ = δ νʲ` on homology in degree `i`, vanishing unless `i = 1 + 4 j`. -/
def homologyδ (k : ℕ) (i : ZMod 8) : C.homology i →ₗ[R] R :=
  (C.moduleCatKerHomologyClass (ChainComplex.next _ i)).liftOfSurjective
    (C.moduleCatKerHomologyClass_surjective _)
    ⟨D.δIter k i ∘ₗ Submodule.subtype _, fun z hz ↦ by
      obtain ⟨⟨_, y, rfl⟩, rfl⟩ := (C.exact_inclusion_moduleCatKerHomologyClass _
        (ChainComplex.prev _ i) z).1 hz
      exact D.δIter_d k _ _ y⟩

/-- `δⱼ` evaluates `δ νʲ` on a representing cycle. -/
@[simp]
lemma homologyδ_moduleCatKerHomologyClass (k : ℕ) (i : ZMod 8)
    (z : LinearMap.ker (C.d i (i - 1)).hom) :
    D.homologyδ k i (C.moduleCatKerHomologyClass (ChainComplex.next _ i) z) = D.δIter k i z :=
  LinearMap.equivOfSurjective_apply _ _

/-- The class `δ'ⱼ` of the cycle `νʲ δ'(1)` in degree `i`, vanishing unless `i = 4 - 4 j`. -/
def homologyδ' (k : ℕ) (i : ZMod 8) : C.homology i :=
  C.moduleCatKerHomologyClass (ChainComplex.next _ i) ⟨D.δ'Iter k i, D.d_δ'Iter k i (i - 1)⟩

/-- `δⱼ δ'ₖ = 0`. -/
@[simp]
lemma homologyδ_homologyδ' (j k : ℕ) (i : ZMod 8) : D.homologyδ j i (D.homologyδ' k i) = 0 := by
  rw [homologyδ', homologyδ_moduleCatKerHomologyClass, δIter_δ'Iter]

/-! ### The reduced subquotient -/

/-- Frøyshov's `Z(I) = ⋂ⱼ ker δⱼ` in degree `i`. -/
def reducedCycles (i : ZMod 8) : Submodule R (C.homology i) :=
  ⨅ k, LinearMap.ker (D.homologyδ k i)

/-- Frøyshov's `B(I) = Σⱼ R δ'ⱼ` in degree `i`. -/
def reducedBoundaries (i : ZMod 8) : Submodule R (C.homology i) :=
  Submodule.span R (Set.range fun k ↦ D.homologyδ' k i)

lemma mem_reducedCycles_iff {i : ZMod 8} {x : C.homology i} :
    x ∈ D.reducedCycles i ↔ ∀ k, D.homologyδ k i x = 0 := by
  simp [reducedCycles]

lemma homologyδ'_mem_reducedBoundaries (k : ℕ) (i : ZMod 8) :
    D.homologyδ' k i ∈ D.reducedBoundaries i :=
  Submodule.subset_span ⟨k, rfl⟩

/-- `B(I) ⊆ Z(I)`. -/
theorem reducedBoundaries_le_reducedCycles (i : ZMod 8) :
    D.reducedBoundaries i ≤ D.reducedCycles i :=
  Submodule.span_le.2 <| Set.range_subset_iff.2 fun k ↦
    D.mem_reducedCycles_iff.2 fun j ↦ D.homologyδ_homologyδ' j k i

/-- The cycles whose classes lie in `B(I)` are the sums of boundaries and of combinations of the
cycles `νʲ δ'(1)`. -/
theorem comap_reducedBoundaries (i : ZMod 8) :
    (D.reducedBoundaries i).comap (C.moduleCatKerHomologyClass (ChainComplex.next _ i)) =
      Submodule.span R (Set.range fun k ↦ ⟨D.δ'Iter k i, D.d_δ'Iter k i (i - 1)⟩) ⊔
        LinearMap.range (Submodule.inclusion (C.range_d_le_ker_d i (i + 1) (i - 1))) := by
  rw [reducedBoundaries, ← LinearMap.exact_iff.1 (C.exact_inclusion_moduleCatKerHomologyClass _
    (ChainComplex.prev _ i)), ← Submodule.comap_map_eq, Submodule.map_span, ← Set.range_comp]
  rfl

/-- The **reduced homology** `Î = Z(I) / B(I)` in degree `i`. -/
abbrev reducedHomology (i : ZMod 8) : Type _ :=
  D.reducedCycles i ⧸ (D.reducedBoundaries i).comap (D.reducedCycles i).subtype

/-- `Z(I)` is the whole homology outside degrees `1` and `5`. -/
theorem reducedCycles_eq_top {i : ZMod 8} (h1 : i ≠ 1) (h5 : i ≠ 5) : D.reducedCycles i = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ D.mem_reducedCycles_iff.2 fun k ↦ ?_
  obtain ⟨z, rfl⟩ := C.moduleCatKerHomologyClass_surjective (ChainComplex.next _ i) x
  rw [homologyδ_moduleCatKerHomologyClass, D.δIter_eq_zero k, LinearMap.zero_apply]
  rintro rfl
  rcases four_mul_natCast k with h | h
  · exact h1 (by rw [h, add_zero])
  · exact h5 (by rw [h]; decide)

/-- `B(I)` vanishes outside degrees `0` and `4`. -/
theorem reducedBoundaries_eq_bot {i : ZMod 8} (h0 : i ≠ 0) (h4 : i ≠ 4) :
    D.reducedBoundaries i = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨k, rfl⟩
  have hk : D.δ'Iter k i = 0 := D.δ'Iter_eq_zero k fun h ↦ by
    rcases four_mul_natCast k with h' | h' <;> rw [h'] at h
    · exact h4 (by simpa using h)
    · exact h0 (by linear_combination h)
  have hk' : (⟨D.δ'Iter k i, D.d_δ'Iter k i (i - 1)⟩ : LinearMap.ker (C.d i (i - 1)).hom) = 0 :=
    Subtype.ext hk
  dsimp only
  rw [homologyδ', hk', map_zero]

/-! ### The descended point map -/

/-- On a cycle `x` whose class lies in `Z(I)`, `ν x` is a cycle: `d ν x = ν d x - 2 δ(x) δ'(1)`
and `δ x = δ₀ [x] = 0`. -/
lemma d_ν_eq_zero {i : ZMod 8} (z : LinearMap.ker (C.d i (i - 1)).hom)
    (hz : C.moduleCatKerHomologyClass (ChainComplex.next _ i) z ∈ D.reducedCycles i) :
    (C.d (i - 4) (i - 4 - 1)).hom (D.ν i (i - 4) z) = 0 := by
  have hδ : D.δ i z = 0 := by
    rw [← δIter_zero, ← homologyδ_moduleCatKerHomologyClass]
    exact D.mem_reducedCycles_iff.1 hz 0
  rw [D.d_ν_apply (sub_add_cancel i 1) (sub_add_cancel _ 1), LinearMap.mem_ker.1 z.property,
    map_zero, hδ, mul_zero, zero_smul, sub_zero]

/-- `ν` maps cycles with classes in `Z(I)` to cycles with classes in `Z(I)`:
`δⱼ [ν x] = δⱼ₊₁ [x]`. -/
lemma moduleCatKerHomologyClass_ν_mem_reducedCycles {i : ZMod 8}
    (z : LinearMap.ker (C.d i (i - 1)).hom)
    (hz : C.moduleCatKerHomologyClass (ChainComplex.next _ i) z ∈ D.reducedCycles i) :
    C.moduleCatKerHomologyClass (ChainComplex.next _ (i - 4))
      ⟨D.ν i (i - 4) z, D.d_ν_eq_zero z hz⟩ ∈ D.reducedCycles (i - 4) :=
  D.mem_reducedCycles_iff.2 fun k ↦ by
    have h := D.mem_reducedCycles_iff.1 hz (k + 1)
    rw [homologyδ_moduleCatKerHomologyClass, δIter_succ, LinearMap.comp_apply] at h
    rw [homologyδ_moduleCatKerHomologyClass]
    exact h

/-- `ν` maps cycles with classes in `B(I)` to elements represented by cycles with classes in
`B(I)`: `ν (νʲ δ'(1)) = νʲ⁺¹ δ'(1)` and `ν (d y) = d (ν y) + 2 δ(y) δ'(1)`. -/
lemma exists_moduleCatKerHomologyClass_mem_reducedBoundaries {i : ZMod 8}
    (z : LinearMap.ker (C.d i (i - 1)).hom)
    (hz : C.moduleCatKerHomologyClass (ChainComplex.next _ i) z ∈ D.reducedBoundaries i) :
    ∃ w : LinearMap.ker (C.d (i - 4) (i - 4 - 1)).hom,
      C.moduleCatKerHomologyClass (ChainComplex.next _ (i - 4)) w ∈ D.reducedBoundaries (i - 4) ∧
        (w : C.X (i - 4)) = D.ν i (i - 4) z := by
  let B := ((D.reducedBoundaries (i - 4)).comap
    (C.moduleCatKerHomologyClass (ChainComplex.next _ (i - 4)))).map (Submodule.subtype _)
  suffices h : ((D.reducedBoundaries i).comap
      (C.moduleCatKerHomologyClass (ChainComplex.next _ i))).map
        (D.ν i (i - 4) ∘ₗ Submodule.subtype _) ≤ B by
    obtain ⟨w, hw, hwz⟩ := h (Submodule.mem_map_of_mem (f := D.ν i (i - 4) ∘ₗ Submodule.subtype _)
      (Submodule.mem_comap.2 hz))
    exact ⟨w, hw, hwz⟩
  have hδ' (k : ℕ) : D.δ'Iter k (i - 4) ∈ B :=
    ⟨⟨D.δ'Iter k (i - 4), D.d_δ'Iter k _ _⟩, D.homologyδ'_mem_reducedBoundaries k _, rfl⟩
  rw [comap_reducedBoundaries, Submodule.map_sup, Submodule.map_span, sup_le_iff,
    Submodule.span_le, ← Set.range_comp]
  refine ⟨Set.range_subset_iff.2 fun k ↦ ?_, ?_⟩
  · simpa [← D.δ'Iter_succ k (sub_add_cancel i 4)] using hδ' (k + 1)
  · rintro _ ⟨_, ⟨⟨_, y, rfl⟩, rfl⟩, rfl⟩
    have h := D.d_ν_apply (m := i) (n := i - 4 + 1) (j := i - 4) rfl rfl y
    rw [eq_sub_iff_add_eq] at h
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.coe_inclusion, ← h]
    refine B.add_mem ⟨⟨_, LinearMap.mem_ker.2 (C.d_comp_d_apply _ _ _ _)⟩, ?_, rfl⟩
      (B.smul_mem _ (hδ' 0))
    rw [SetLike.mem_coe, Submodule.mem_comap]
    convert zero_mem (D.reducedBoundaries (i - 4))
    exact LinearMap.mem_ker.1 ((LinearMap.exact_iff.1 (C.exact_inclusion_moduleCatKerHomologyClass _
      (ChainComplex.prev _ (i - 4)))).ge ⟨⟨_, _, rfl⟩, rfl⟩)

/-- The class map from the cycles whose classes lie in `Z(I)` onto `Î`. -/
private def toReducedHomology (i : ZMod 8) :
    (D.reducedCycles i).comap (C.moduleCatKerHomologyClass (ChainComplex.next _ i)) →ₗ[R]
      D.reducedHomology i :=
  ((D.reducedBoundaries i).comap (D.reducedCycles i).subtype).mkQ ∘ₗ
    (C.moduleCatKerHomologyClass (ChainComplex.next _ i)).restrict (q := D.reducedCycles i)
      fun _ h ↦ h

private lemma toReducedHomology_surjective (i : ZMod 8) :
    Function.Surjective (D.toReducedHomology i) := by
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z, rfl⟩ := C.moduleCatKerHomologyClass_surjective (ChainComplex.next _ i) x
  exact ⟨⟨z, hx⟩, rfl⟩

/-- The map `x ↦ [ν x]` from the cycles whose classes lie in `Z(I)` to `Î` in degree `i - 4`. -/
private def toReducedHomologyν (i : ZMod 8) :
    (D.reducedCycles i).comap (C.moduleCatKerHomologyClass (ChainComplex.next _ i)) →ₗ[R]
      D.reducedHomology (i - 4) :=
  D.toReducedHomology (i - 4) ∘ₗ LinearMap.codRestrict _
    (LinearMap.codRestrict _ (D.ν i (i - 4) ∘ₗ Submodule.subtype _ ∘ₗ Submodule.subtype _)
      fun z ↦ D.d_ν_eq_zero z.val z.property)
    fun z ↦ D.moduleCatKerHomologyClass_ν_mem_reducedCycles z.val z.property

private lemma ker_toReducedHomology_le (i : ZMod 8) :
    LinearMap.ker (D.toReducedHomology i) ≤ LinearMap.ker (D.toReducedHomologyν i) := by
  intro z hz
  simp only [LinearMap.mem_ker, toReducedHomology, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
    LinearMap.restrict_apply] at hz
  obtain ⟨w, hw, hwz⟩ := D.exists_moduleCatKerHomologyClass_mem_reducedBoundaries z.val hz
  simp only [LinearMap.mem_ker, toReducedHomologyν, toReducedHomology, LinearMap.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.subtype_apply, LinearMap.restrict_apply]
  convert hw using 2
  exact Subtype.ext hwz.symm

/-- The **point map** `u : Îᵢ → Îᵢ₋₄` induced by `ν` on the reduced homology. -/
def reducedPointMap (i : ZMod 8) : D.reducedHomology i →ₗ[R] D.reducedHomology (i - 4) :=
  (D.toReducedHomology i).liftOfSurjective (D.toReducedHomology_surjective i)
    ⟨D.toReducedHomologyν i, D.ker_toReducedHomology_le i⟩

/-- `u [x] = [ν x]` for a cycle `x` whose class lies in `Z(I)`. -/
theorem reducedPointMap_mk {i : ZMod 8} (z : LinearMap.ker (C.d i (i - 1)).hom)
    (hz : C.moduleCatKerHomologyClass (ChainComplex.next _ i) z ∈ D.reducedCycles i) :
    D.reducedPointMap i
        (Submodule.Quotient.mk ⟨C.moduleCatKerHomologyClass (ChainComplex.next _ i) z, hz⟩) =
      Submodule.Quotient.mk ⟨C.moduleCatKerHomologyClass (ChainComplex.next _ (i - 4))
        ⟨D.ν i (i - 4) z, D.d_ν_eq_zero z hz⟩,
        D.moduleCatKerHomologyClass_ν_mem_reducedCycles z hz⟩ :=
  LinearMap.equivOfSurjective_apply (f := D.toReducedHomology i) _ (m := ⟨z, hz⟩) _

end ReducibleMaps

end TauCeti.Instanton
