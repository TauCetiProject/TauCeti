/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.OfTriple
import Mathlib.GroupTheory.Perm.Cycle.Concrete
-- Kernel reduction of the finite searches needs the unexposed cycle-data and cycle-factor bodies.
import all TauCeti.Combinatorics.PermutationTriple.CycleData
import all Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Classification of connected triples in small degrees

Through degree four, the ordered full cycle partitions determine a connected permutation
triple up to simultaneous relabeling. Consequently every inhabited ordered passport in these
degrees has size one, even without using its monodromy subgroup to distinguish classes.

The cycle-data tables list all three degree-two classes, all seven degree-three classes, and
all twenty-six degree-four classes. The degree-four table also determines their genera and
geometry types: six classes have genus one, four are Euclidean, three are hyperbolic, and the
rest are spherical. Fixed points are included in every displayed partition.

The degree-four representatives realize exactly the cycle data in the table, and every connected
degree-four triple is equivalent to one of them. Consequently the table classifies connected
triples up to relabeling, determines their Euler characteristics, genera, and geometry types,
counts the twenty-six isomorphism classes, and shows that every inhabited ordered passport through
degree four contains a single class.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5.
-/

open Equiv

public section

namespace TauCeti

namespace PermutationTriple

/-- The twenty-six ordered cycle data realized by connected degree-four permutation triples. -/
def degreeFourCycleData : Finset (Multiset ℕ × Multiset ℕ × Multiset ℕ) :=
  {({1, 1, 1, 1}, {4}, {4}),
    ({2, 1, 1}, {2, 2}, {4}), ({2, 1, 1}, {3, 1}, {4}),
    ({2, 1, 1}, {4}, {2, 2}), ({2, 1, 1}, {4}, {3, 1}),
    ({2, 2}, {2, 1, 1}, {4}), ({2, 2}, {2, 2}, {2, 2}),
    ({2, 2}, {3, 1}, {3, 1}), ({2, 2}, {4}, {2, 1, 1}),
    ({2, 2}, {4}, {4}),
    ({3, 1}, {2, 1, 1}, {4}), ({3, 1}, {2, 2}, {3, 1}),
    ({3, 1}, {3, 1}, {2, 2}), ({3, 1}, {3, 1}, {3, 1}),
    ({3, 1}, {4}, {2, 1, 1}), ({3, 1}, {4}, {4}),
    ({4}, {1, 1, 1, 1}, {4}),
    ({4}, {2, 1, 1}, {2, 2}), ({4}, {2, 1, 1}, {3, 1}),
    ({4}, {2, 2}, {2, 1, 1}), ({4}, {2, 2}, {4}),
    ({4}, {3, 1}, {2, 1, 1}), ({4}, {3, 1}, {4}),
    ({4}, {4}, {1, 1, 1, 1}), ({4}, {4}, {2, 2}), ({4}, {4}, {3, 1})}

/-- One permutation of `Fin 4` of each cycle type. -/
private def degreeFourCycleTypeReps : List (Perm (Fin 4)) :=
  [1, c[0, 1], c[0, 1] * c[2, 3], c[0, 1, 2], c[0, 1, 2, 3]]

/-- One connected degree-four triple from each isomorphism class, in the order of
`degreeFourCycleData`, each with first component in `degreeFourCycleTypeReps`. -/
private def degreeFourClassReps : List (PermutationTriple 4) :=
  [ofTwo 1 c[0, 1, 2, 3],
    ofTwo c[0, 1] (c[0, 2] * c[1, 3]), ofTwo c[0, 1] c[0, 2, 3],
    ofTwo c[0, 1] c[0, 2, 1, 3], ofTwo c[0, 1] c[0, 1, 2, 3],
    ofTwo (c[0, 1] * c[2, 3]) c[0, 2], ofTwo (c[0, 1] * c[2, 3]) (c[0, 2] * c[1, 3]),
    ofTwo (c[0, 1] * c[2, 3]) c[0, 1, 2], ofTwo (c[0, 1] * c[2, 3]) c[0, 1, 2, 3],
    ofTwo (c[0, 1] * c[2, 3]) c[0, 2, 1, 3],
    ofTwo c[0, 1, 2] c[0, 3], ofTwo c[0, 1, 2] (c[0, 1] * c[2, 3]),
    ofTwo c[0, 1, 2] c[0, 1, 3], ofTwo c[0, 1, 2] c[0, 2, 3],
    ofTwo c[0, 1, 2] c[0, 2, 1, 3], ofTwo c[0, 1, 2] c[0, 1, 2, 3],
    ofTwo c[0, 1, 2, 3] 1,
    ofTwo c[0, 1, 2, 3] c[0, 2], ofTwo c[0, 1, 2, 3] c[0, 1],
    ofTwo c[0, 1, 2, 3] (c[0, 1] * c[2, 3]), ofTwo c[0, 1, 2, 3] (c[0, 2] * c[1, 3]),
    ofTwo c[0, 1, 2, 3] c[0, 2, 1], ofTwo c[0, 1, 2, 3] c[0, 1, 2],
    ofTwo c[0, 1, 2, 3] c[0, 3, 2, 1], ofTwo c[0, 1, 2, 3] c[0, 1, 2, 3],
    ofTwo c[0, 1, 2, 3] c[0, 1, 3, 2]]

private theorem exists_conj_mem_degreeFourCycleTypeReps :
    ∀ σ : Perm (Fin 4), ∃ τ : Perm (Fin 4), τ * σ * τ⁻¹ ∈ degreeFourCycleTypeReps := by
  decide +kernel

private theorem exists_smul_ofTwo_mem_degreeFourClassReps :
    ∀ σ0 ∈ degreeFourCycleTypeReps, ∀ σ1 : Perm (Fin 4), (ofTwo σ0 σ1).IsConnected →
      ∃ τ : Perm (Fin 4), τ • ofTwo σ0 σ1 ∈ degreeFourClassReps := by
  decide +kernel

private theorem isConnected_of_mem_degreeFourClassReps :
    ∀ r ∈ degreeFourClassReps, r.IsConnected := by
  decide +kernel

private theorem nodup_map_cycleData_degreeFourClassReps :
    (degreeFourClassReps.map cycleData).Nodup := by
  decide +kernel

private theorem toFinset_map_cycleData_degreeFourClassReps :
    (degreeFourClassReps.map cycleData).toFinset = degreeFourCycleData := by
  decide +kernel

/-- Every connected degree-four triple is a relabeling of one of the representatives. -/
private theorem exists_smul_mem_degreeFourClassReps (t : ConnectedTriple 4) :
    ∃ τ : Perm (Fin 4), τ • t.1 ∈ degreeFourClassReps := by
  obtain ⟨τ₀, hτ₀⟩ := exists_conj_mem_degreeFourCycleTypeReps t.1.σ0
  have ht : τ₀ • t.1 = ofTwo (τ₀ * t.1.σ0 * τ₀⁻¹) (τ₀ * t.1.σ1 * τ₀⁻¹) := ext_of_two rfl rfl
  obtain ⟨τ₁, hτ₁⟩ := exists_smul_ofTwo_mem_degreeFourClassReps _ hτ₀ _ <| by
    rw [← ht]
    exact (isConnected_smul_iff τ₀ t.1).2 t.2
  exact ⟨τ₁ * τ₀, by rwa [mul_smul, ht]⟩

/-- The complete table of ordered full cycle data in degree four. -/
theorem image_cycleData_four :
    (Finset.univ : Finset (ConnectedTriple 4)).image (fun t => t.1.cycleData) =
      degreeFourCycleData := by
  rw [← toFinset_map_cycleData_degreeFourClassReps]
  ext d
  simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨τ, hτ⟩ := exists_smul_mem_degreeFourClassReps t
    exact ⟨τ • t.1, hτ, cycleData_smul τ t.1⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨r, isConnected_of_mem_degreeFourClassReps r hr⟩, rfl⟩

/-- The ordered full cycle data of every connected degree-four triple appear in the table
`degreeFourCycleData`. -/
@[simp]
theorem cycleData_mem_degreeFourCycleData (t : ConnectedTriple 4) :
    t.1.cycleData ∈ degreeFourCycleData := by
  rw [← image_cycleData_four]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ t)

private theorem equivalent_of_cycleData_eq_two :
    ∀ t t' : ConnectedTriple 2, t.1.cycleData = t'.1.cycleData → Equivalent t.1 t'.1 := by
  decide +kernel

private theorem equivalent_of_cycleData_eq_three :
    ∀ t t' : ConnectedTriple 3, t.1.cycleData = t'.1.cycleData → Equivalent t.1 t'.1 := by
  decide +kernel

private theorem equivalent_of_cycleData_eq_four (t t' : ConnectedTriple 4)
    (h : t.1.cycleData = t'.1.cycleData) : Equivalent t.1 t'.1 := by
  obtain ⟨τ, hτ⟩ := exists_smul_mem_degreeFourClassReps t
  obtain ⟨τ', hτ'⟩ := exists_smul_mem_degreeFourClassReps t'
  have hr : τ • t.1 = τ' • t'.1 :=
    List.inj_on_of_nodup_map nodup_map_cycleData_degreeFourClassReps hτ hτ' <| by
      rw [cycleData_smul, cycleData_smul, h]
  exact equivalent_iff_exists_smul_eq.mpr ⟨τ'⁻¹ * τ, by rw [mul_smul, hr, inv_smul_smul]⟩

/-- Through degree four, the ordered full cycle partitions classify connected triples up to
simultaneous relabeling. The monodromy group is not needed as an additional invariant. -/
theorem equivalent_iff_cycleData_eq_of_degree_le_four {n : ℕ} (hn : n ≤ 4)
    (t t' : ConnectedTriple n) : Equivalent t.1 t'.1 ↔ t.1.cycleData = t'.1.cycleData := by
  refine ⟨cycleData_eq_of_equivalent, fun h => ?_⟩
  have hn0 := t.2.ne_zero
  interval_cases n
  · exact (hn0 rfl).elim
  · have ht : t.1 = t'.1 := Subsingleton.elim _ _
    rw [ht]
    exact equivalent_iff_exists_smul_eq.mpr ⟨1, one_smul _ _⟩
  · exact equivalent_of_cycleData_eq_two t t' h
  · exact equivalent_of_cycleData_eq_three t t' h
  · exact equivalent_of_cycleData_eq_four t t' h

/-- The unique ordered cycle datum in degree one. -/
theorem image_cycleData_one :
    (Finset.univ : Finset (ConnectedTriple 1)).image (fun t => t.1.cycleData) =
      {({1}, {1}, {1})} := by
  decide +kernel

/-- The complete table of ordered full cycle data in degree two. The three classes differ by
which branch point is unramified. -/
theorem image_cycleData_two :
    (Finset.univ : Finset (ConnectedTriple 2)).image (fun t => t.1.cycleData) =
      {({1, 1}, {2}, {2}), ({2}, {1, 1}, {2}), ({2}, {2}, {1, 1})} := by
  decide +kernel

/-- The complete table of ordered full cycle data in degree three. There are three cyclic
spherical classes, three nonabelian spherical classes, and one cyclic Euclidean class. -/
theorem image_cycleData_three :
    (Finset.univ : Finset (ConnectedTriple 3)).image (fun t => t.1.cycleData) =
      {({1, 1, 1}, {3}, {3}), ({3}, {1, 1, 1}, {3}), ({3}, {3}, {1, 1, 1}),
        ({2, 1}, {2, 1}, {3}), ({2, 1}, {3}, {2, 1}), ({3}, {2, 1}, {2, 1}),
        ({3}, {3}, {3})} := by
  decide +kernel

/-- A connected degree-four triple has Euler characteristic zero precisely for the six cycle
data obtained by placing two full four-cycles beside either two two-cycles or a three-cycle and
a fixed point; all other degree-four classes have Euler characteristic two. -/
theorem eulerChar_eq_ite_of_degree_four (t : ConnectedTriple 4) :
    t.1.eulerChar = if t.1.cycleData ∈
      ({({2, 2}, {4}, {4}), ({4}, {2, 2}, {4}), ({4}, {4}, {2, 2}),
        ({3, 1}, {4}, {4}), ({4}, {3, 1}, {4}), ({4}, {4}, {3, 1})} :
          Finset (Multiset ℕ × Multiset ℕ × Multiset ℕ))
    then 0 else 2 := by
  have hd := cycleData_mem_degreeFourCycleData t
  simp only [degreeFourCycleData, Finset.mem_insert, Finset.mem_singleton] at hd
  rw [eulerChar_eq_cycleCounts, cycleCounts_eq_card_cycleData]
  rcases hd with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd |
    hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd <;>
    rw [hd] <;> decide +kernel

/-- A connected degree-four triple has genus one precisely for the six cycle data obtained by
placing two full four-cycles beside either two two-cycles or a three-cycle and a fixed point;
all other degree-four classes have genus zero. -/
theorem genus_eq_ite_of_degree_four (t : ConnectedTriple 4) :
    t.1.genus = if t.1.cycleData ∈
      ({({2, 2}, {4}, {4}), ({4}, {2, 2}, {4}), ({4}, {4}, {2, 2}),
        ({3, 1}, {4}, {4}), ({4}, {3, 1}, {4}), ({4}, {4}, {3, 1})} :
          Finset (Multiset ℕ × Multiset ℕ × Multiset ℕ))
    then 1 else 0 := by
  rw [genus_def, eulerChar_eq_ite_of_degree_four]
  split_ifs <;> norm_num

/-- The exact geometry type of a connected degree-four triple, read from its ordered full cycle
data. The three permutations of `([3,1], [4], [4])` are hyperbolic; the three permutations of
`([2,2], [4], [4])` and `([3,1], [3,1], [3,1])` are Euclidean; all others are spherical. -/
theorem geometryType_eq_ite_of_degree_four (t : ConnectedTriple 4) :
    t.1.geometryType =
      if t.1.cycleData ∈
        ({({3, 1}, {4}, {4}), ({4}, {3, 1}, {4}), ({4}, {4}, {3, 1})} :
          Finset (Multiset ℕ × Multiset ℕ × Multiset ℕ))
      then .hyperbolic
      else if t.1.cycleData ∈
        ({({2, 2}, {4}, {4}), ({4}, {2, 2}, {4}), ({4}, {4}, {2, 2}),
          ({3, 1}, {3, 1}, {3, 1})} :
            Finset (Multiset ℕ × Multiset ℕ × Multiset ℕ))
      then .euclidean
      else .spherical := by
  have hd := cycleData_mem_degreeFourCycleData t
  simp only [degreeFourCycleData, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd |
    hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd
  all_goals
    simp (disch := decide) only [hd, Finset.mem_insert, Finset.mem_singleton]
    first
    | apply (geometryType_eq_spherical_iff t.1).mpr
    | apply (geometryType_eq_euclidean_iff t.1).mpr
    | apply (geometryType_eq_hyperbolic_iff t.1).mpr
    simp only [← orderTriple_σ0, ← orderTriple_σ1, ← orderTriple_σinf,
      orderTriple_eq_lcm_cycleData]
    norm_num [hd]

/-- Through degree three, the Euler characteristic is zero for the triple with three full
three-cycles, and two for every other connected triple. -/
theorem eulerChar_eq_ite_of_degree_le_three {n : ℕ} (hn : n ≤ 3)
    (t : ConnectedTriple n) :
    t.1.eulerChar = if t.1.cycleData = ({3}, {3}, {3}) then 0 else 2 := by
  have hn0 := t.2.ne_zero
  have hd : t.1.cycleData ∈
      (Finset.univ : Finset (ConnectedTriple n)).image (fun s => s.1.cycleData) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ t)
  rw [eulerChar_eq_cycleCounts, cycleCounts_eq_card_cycleData]
  interval_cases n
  · exact (hn0 rfl).elim
  · rw [image_cycleData_one] at hd
    simp only [Finset.mem_singleton] at hd
    norm_num [hd]
  · rw [image_cycleData_two] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with hd | hd | hd <;> norm_num [hd]
  · rw [image_cycleData_three] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd <;> norm_num [hd] <;> decide

/-- The unique positive-genus class through degree three is the class with full cycle
partition `[3]` at all three branch points, and it has genus one. -/
theorem genus_eq_ite_of_degree_le_three {n : ℕ} (hn : n ≤ 3)
    (t : ConnectedTriple n) :
    t.1.genus = if t.1.cycleData = ({3}, {3}, {3}) then 1 else 0 := by
  rw [genus_def, eulerChar_eq_ite_of_degree_le_three hn t]
  split_ifs <;> norm_num

/-- The class with three full three-cycles is Euclidean; every other connected class through
degree three is spherical. -/
theorem geometryType_eq_ite_of_degree_le_three {n : ℕ} (hn : n ≤ 3)
    (t : ConnectedTriple n) :
    t.1.geometryType =
      if t.1.cycleData = ({3}, {3}, {3}) then .euclidean else .spherical := by
  split_ifs with h
  · apply (geometryType_eq_euclidean_iff t.1).mpr
    simp only [← orderTriple_σ0, ← orderTriple_σ1, ← orderTriple_σinf,
      orderTriple_eq_lcm_cycleData]
    norm_num [h]
  · apply (geometryType_eq_spherical_iff t.1).mpr
    simp only [← orderTriple_σ0, ← orderTriple_σ1, ← orderTriple_σinf,
      orderTriple_eq_lcm_cycleData]
    have hn0 := t.2.ne_zero
    have hd : t.1.cycleData ∈
        (Finset.univ : Finset (ConnectedTriple n)).image (fun s => s.1.cycleData) :=
      Finset.mem_image_of_mem _ (Finset.mem_univ t)
    interval_cases n
    · exact (hn0 rfl).elim
    · rw [image_cycleData_one] at hd
      simp only [Finset.mem_singleton] at hd
      norm_num [hd]
    · rw [image_cycleData_two] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with hd | hd | hd <;> norm_num [hd]
    · rw [image_cycleData_three] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with hd | hd | hd | hd | hd | hd | hd
      all_goals norm_num [hd]
      exact h hd

end PermutationTriple

namespace ConnectedIsoClass

/-- There are twenty-six isomorphism classes of connected permutation triples of degree four. -/
theorem card_four : Fintype.card (ConnectedIsoClass 4) = 26 := by
  let f : ConnectedIsoClass 4 → {d // d ∈ PermutationTriple.degreeFourCycleData} := fun c =>
    Quotient.liftOn' c
      (fun t => ⟨t.1.cycleData, PermutationTriple.cycleData_mem_degreeFourCycleData t⟩)
      fun t t' h => Subtype.ext <| PermutationTriple.cycleData_eq_of_equivalent <|
        mk_eq_mk_iff_equivalent.mp (Quotient.sound' h)
  have hf : Function.Bijective f := by
    refine ⟨fun c c' h => ?_, fun d => ?_⟩
    · obtain ⟨t, rfl⟩ := mk_surjective c
      obtain ⟨t', rfl⟩ := mk_surjective c'
      exact mk_eq_mk_iff_equivalent.mpr
        (PermutationTriple.equivalent_of_cycleData_eq_four t t' (congrArg Subtype.val h))
    · have hd : d.1 ∈ (Finset.univ : Finset (ConnectedTriple 4)).image
          (fun t => t.1.cycleData) := by
        rw [PermutationTriple.image_cycleData_four]
        exact d.2
      obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hd
      exact ⟨mk t, Subtype.ext ht⟩
  rw [Fintype.card_of_bijective hf, Fintype.card_coe]
  decide

end ConnectedIsoClass

namespace PassportSpec

variable {n : ℕ}

/-- Through degree four, an inhabited ordered passport consists of exactly one isomorphism
class. This is stronger than bounding its size: the class is identified by any member. -/
theorem classSet_eq_singleton_of_degree_le_four (hn : n ≤ 4) (P : PassportSpec n)
    (t : ConnectedTriple n) (ht : HasPassport t P) :
    P.classSet = {ConnectedIsoClass.mk t} := by
  classical
  ext c
  obtain ⟨s, rfl⟩ := ConnectedIsoClass.mk_surjective c
  simp only [mem_classSet, ConnectedIsoClass.hasPassport_mk, Finset.mem_singleton]
  constructor
  · intro hs
    apply ConnectedIsoClass.mk_eq_mk_iff_equivalent.mpr
    exact (PermutationTriple.equivalent_iff_cycleData_eq_of_degree_le_four hn s t).mpr
      (cycleData_eq_of_hasPassport hs ht)
  · intro h
    have hc := (ConnectedIsoClass.hasPassport_mk t P).mpr ht
    rw [← h] at hc
    exact (ConnectedIsoClass.hasPassport_mk s P).mp hc

/-- Through degree four, a passport has size one exactly when it is inhabited. Admissibility
alone is not substituted for existence of a product-one triple. -/
theorem passportSize_eq_one_iff_of_degree_le_four (hn : n ≤ 4) (P : PassportSpec n) :
    P.passportSize = 1 ↔ ∃ t : ConnectedTriple n, HasPassport t P := by
  constructor
  · intro h
    exact (passportSize_pos_iff P).mp (by omega)
  · rintro ⟨t, ht⟩
    rw [passportSize_def, classSet_eq_singleton_of_degree_le_four hn P t ht,
      Finset.card_singleton]

/-- Every ordered passport in degree at most four has size zero or one. -/
theorem passportSize_le_one_of_degree_le_four (hn : n ≤ 4) (P : PassportSpec n) :
    P.passportSize ≤ 1 := by
  by_cases h : 0 < P.passportSize
  · obtain ⟨t, ht⟩ := (passportSize_pos_iff P).mp h
    rw [(passportSize_eq_one_iff_of_degree_le_four hn P).mpr ⟨t, ht⟩]
  · omega

end PassportSpec

namespace ConnectedTriple

/-- The ordered passport of any connected triple through degree four has size one. -/
theorem passportSize_passportOf_of_degree_le_four {n : ℕ} (hn : n ≤ 4)
    (t : ConnectedTriple n) : t.passportOf.passportSize = 1 :=
  (PassportSpec.passportSize_eq_one_iff_of_degree_le_four hn t.passportOf).mpr
    ⟨t, t.hasPassport_passportOf⟩

end ConnectedTriple

end TauCeti
