/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cohomology

/-!
# Triple Massey products of A-infinity algebras

Let `x`, `y`, `z` be cohomology classes of an `A∞` algebra with `x y = 0` and `y z = 0`.  Choose
cycles `a`, `b`, `c` representing them and cochains `u`, `v` with `m₁ u = m₂ (a, b)` and
`m₁ v = m₂ (b, c)`; such a choice is a *defining system*.  The cochain

`m₂ (u, c) - m₂ (τ a, v) + m₃ (a, b, c)`,

with `τ` the degree-one Koszul twist (the sign `(-1)^{|a|}` on homogeneous `a`), is a cycle by
the Leibniz rule and the arity-three Stasheff identity.  The **triple Massey product**
`⟨x, y, z⟩` is the set of the classes of these cycles over all defining systems.

The Massey product is a set, not an element: it is nonempty exactly when `x y = 0` and
`y z = 0`, and then it is a coset of the **indeterminacy** `τx · H + H · z`.  Both inclusions
are proved here.  Adding an element of the indeterminacy amounts to changing `u` and `v` by
cycles.  Conversely, two defining systems are connected by changing the representatives `a`, `b`,
`c` one at a time, each change altering the cycle by a boundary, followed by changing `u` and `v`
by cycles.  On a homogeneous class `x` the twist is a sign, so the indeterminacy is the classical
`x · H + H · z`.

For a DG algebra (`m₃ = 0`) and homogeneous classes this is May's triple Massey product up to the
sign `(-1)^{|y|+1}`; the ternary operation corrects the cochain for the failure of `m₂` to be
associative.  Over a field, the ternary operation of the minimal model on cohomology selects an
element of `⟨x, y, z⟩`; that comparison lives in
`TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Massey`.

## Main definitions

* `TauCeti.AInfinityAlgebra.TripleMasseyDefiningSystem`: a defining system for `⟨x, y, z⟩`.
* `TauCeti.AInfinityAlgebra.TripleMasseyDefiningSystem.cycle`: its Massey cycle.
* `TauCeti.AInfinityAlgebra.TripleMasseyDefiningSystem.value`: the class of its Massey cycle.
* `TauCeti.AInfinityAlgebra.tripleMasseyProduct`: the triple Massey product `⟨x, y, z⟩`.
* `TauCeti.AInfinityAlgebra.tripleMasseyIndeterminacy`: the indeterminacy `τx · H + H · z`.

## Main results

* `TauCeti.AInfinityAlgebra.tripleMasseyProduct_nonempty_iff`: the Massey product is defined
  exactly when `x y = 0` and `y z = 0`.
* `TauCeti.AInfinityAlgebra.add_mem_tripleMasseyProduct`: the Massey product is stable under
  adding its indeterminacy.
* `TauCeti.AInfinityAlgebra.sub_mem_tripleMasseyIndeterminacy`: two elements of the Massey product
  differ by an element of the indeterminacy.
* `TauCeti.AInfinityAlgebra.mem_tripleMasseyProduct_iff_sub_mem`: the Massey product is a coset of
  the indeterminacy.
* `TauCeti.AInfinityAlgebra.tripleMasseyIndeterminacy_eq_of_mem_piece`: on a homogeneous class the
  indeterminacy is `x · H + H · z`.

## References

* J. P. May, *Matric Massey products*, J. Algebra 12 (1969), 533--568, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.3.
-/

public section

namespace TauCeti.AInfinityAlgebra

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  (𝒜 : AInfinityAlgebra R A)

/-- The binary operation vanishes on a zero left input. -/
private theorem m_two_zero_left (y : A) : 𝒜.m 2 ![0, y] = 0 := (𝒜.m 2).map_coord_zero 0 rfl

/-- The binary operation vanishes on a zero right input. -/
private theorem m_two_zero_right (x : A) : 𝒜.m 2 ![x, 0] = 0 := (𝒜.m 2).map_coord_zero 1 rfl

/-- The ternary operation vanishes on a zero first input. -/
private theorem m_three_zero₀ (y z : A) : 𝒜.m 3 ![0, y, z] = 0 := (𝒜.m 3).map_coord_zero 0 rfl

/-- The ternary operation vanishes on a zero second input. -/
private theorem m_three_zero₁ (x z : A) : 𝒜.m 3 ![x, 0, z] = 0 := (𝒜.m 3).map_coord_zero 1 rfl

/-- The ternary operation vanishes on a zero third input. -/
private theorem m_three_zero₂ (x y : A) : 𝒜.m 3 ![x, y, 0] = 0 := (𝒜.m 3).map_coord_zero 2 rfl

/-- The ternary operation is additive in its first input. -/
private theorem m_three_add₀ (x x' y z : A) :
    𝒜.m 3 ![x + x', y, z] = 𝒜.m 3 ![x, y, z] + 𝒜.m 3 ![x', y, z] := by
  convert (𝒜.m 3).map_update_add ![x, y, z] 0 x x' using 2 <;>
    congr 1 <;> funext i <;> fin_cases i <;> rfl

/-- The ternary operation is additive in its second input. -/
private theorem m_three_add₁ (x y y' z : A) :
    𝒜.m 3 ![x, y + y', z] = 𝒜.m 3 ![x, y, z] + 𝒜.m 3 ![x, y', z] := by
  convert (𝒜.m 3).map_update_add ![x, y, z] 1 y y' using 2 <;>
    congr 1 <;> funext i <;> fin_cases i <;> rfl

/-- The ternary operation is additive in its third input. -/
private theorem m_three_add₂ (x y z z' : A) :
    𝒜.m 3 ![x, y, z + z'] = 𝒜.m 3 ![x, y, z] + 𝒜.m 3 ![x, y, z'] := by
  convert (𝒜.m 3).map_update_add ![x, y, z] 2 z z' using 2 <;>
    congr 1 <;> funext i <;> fin_cases i <;> rfl

/-- The class of a cycle written as a sum of three cycles is the sum of their classes. -/
private theorem cohomologyClass_eq_add_add {X Y Z W : A} (hX : X ∈ 𝒜.cycles)
    (hY : Y ∈ 𝒜.cycles) (hZ : Z ∈ 𝒜.cycles) (hW : W ∈ 𝒜.cycles) (h : W = X + (Y + Z)) :
    𝒜.cohomologyClass hW =
      𝒜.cohomologyClass hX + (𝒜.cohomologyClass hY + 𝒜.cohomologyClass hZ) := by
  subst h
  rw [← cohomologyClass_add, ← cohomologyClass_add]

/-! ### Defining systems -/

/-- A **defining system** for the triple Massey product `⟨x, y, z⟩`: cycles `a`, `b`, `c`
representing `x`, `y`, `z`, together with cochains `u` and `v` bounding the products of adjacent
representatives, `m₁ u = m₂ (a, b)` and `m₁ v = m₂ (b, c)`. -/
structure TripleMasseyDefiningSystem (x y z : 𝒜.Cohomology) where
  /-- The representative of `x`. -/
  a : A
  /-- The representative of `y`. -/
  b : A
  /-- The representative of `z`. -/
  c : A
  /-- The cochain bounding `m₂ (a, b)`. -/
  u : A
  /-- The cochain bounding `m₂ (b, c)`. -/
  v : A
  /-- The representative of `x` is a cycle. -/
  a_mem_cycles : a ∈ 𝒜.cycles
  /-- The representative of `y` is a cycle. -/
  b_mem_cycles : b ∈ 𝒜.cycles
  /-- The representative of `z` is a cycle. -/
  c_mem_cycles : c ∈ 𝒜.cycles
  /-- The cycle `a` represents `x`. -/
  cohomologyClass_a : 𝒜.cohomologyClass a_mem_cycles = x
  /-- The cycle `b` represents `y`. -/
  cohomologyClass_b : 𝒜.cohomologyClass b_mem_cycles = y
  /-- The cycle `c` represents `z`. -/
  cohomologyClass_c : 𝒜.cohomologyClass c_mem_cycles = z
  /-- The cochain `u` bounds `m₂ (a, b)`. -/
  m_one_u : 𝒜.m 1 ![u] = 𝒜.m 2 ![a, b]
  /-- The cochain `v` bounds `m₂ (b, c)`. -/
  m_one_v : 𝒜.m 1 ![v] = 𝒜.m 2 ![b, c]

namespace TripleMasseyDefiningSystem

variable {𝒜} {x y z : 𝒜.Cohomology} (S : 𝒜.TripleMasseyDefiningSystem x y z)

/-- The **Massey cycle** `m₂ (u, c) - m₂ (τ a, v) + m₃ (a, b, c)` of a defining system, with `τ`
the degree-one Koszul twist. -/
noncomputable def cycle : A :=
  𝒜.m 2 ![S.u, S.c] - 𝒜.m 2 ![𝒜.grading.koszulTwist 1 S.a, S.v] + 𝒜.m 3 ![S.a, S.b, S.c]

/-- The Massey cycle, unfolded. -/
theorem cycle_def : S.cycle =
    𝒜.m 2 ![S.u, S.c] - 𝒜.m 2 ![𝒜.grading.koszulTwist 1 S.a, S.v] +
      𝒜.m 3 ![S.a, S.b, S.c] := (rfl)

/-- The Massey cycle of a defining system is a cycle. -/
theorem cycle_mem_cycles : S.cycle ∈ 𝒜.cycles := by
  have ha := 𝒜.mem_cycles.mp S.a_mem_cycles
  have hb := 𝒜.mem_cycles.mp S.b_mem_cycles
  have hc := 𝒜.mem_cycles.mp S.c_mem_cycles
  rw [mem_cycles, ← differential_apply, cycle_def, map_add, map_sub]
  simp only [differential_apply, m_one_m_two, m_one_m_three, m_one_koszulTwist,
    InternalGrading.koszulTwist_koszulTwist, S.m_one_u, S.m_one_v, ha, hb, hc, map_zero,
    neg_zero, m_three_zero₀, m_three_zero₁, m_three_zero₂, m_two_zero_left, m_two_zero_right]
  abel

/-- The class of the Massey cycle of a defining system: an element of the triple Massey
product. -/
noncomputable def value : 𝒜.Cohomology :=
  𝒜.cohomologyClass S.cycle_mem_cycles

/-- The value of a defining system is the class of its Massey cycle. -/
theorem value_def : S.value = 𝒜.cohomologyClass S.cycle_mem_cycles := (rfl)

end TripleMasseyDefiningSystem

/-! ### The triple Massey product and its indeterminacy -/

/-- The **triple Massey product** `⟨x, y, z⟩`: the set of classes of the Massey cycles of all
defining systems. -/
noncomputable def tripleMasseyProduct (x y z : 𝒜.Cohomology) : Set 𝒜.Cohomology :=
  Set.range (TripleMasseyDefiningSystem.value (𝒜 := 𝒜) (x := x) (y := y) (z := z))

/-- The **indeterminacy** `τx · H + H · z` of the triple Massey product `⟨x, y, z⟩`, with `τ` the
degree-one Koszul twist. -/
noncomputable def tripleMasseyIndeterminacy (x z : 𝒜.Cohomology) : Submodule R 𝒜.Cohomology :=
  LinearMap.range (LinearMap.mulLeft R (𝒜.cohomologyGrading.koszulTwist 1 x)) ⊔
    LinearMap.range (LinearMap.mulRight R z)

variable {𝒜} {x y z : 𝒜.Cohomology}

/-- An element of `⟨x, y, z⟩` is the value of some defining system. -/
theorem mem_tripleMasseyProduct {w : 𝒜.Cohomology} :
    w ∈ 𝒜.tripleMasseyProduct x y z ↔
      ∃ S : 𝒜.TripleMasseyDefiningSystem x y z, S.value = w :=
  Iff.rfl

/-- The value of a defining system lies in the triple Massey product. -/
theorem TripleMasseyDefiningSystem.value_mem (S : 𝒜.TripleMasseyDefiningSystem x y z) :
    S.value ∈ 𝒜.tripleMasseyProduct x y z :=
  ⟨S, rfl⟩

/-- The elements of the indeterminacy are the sums `τx * s + t * z`. -/
theorem mem_tripleMasseyIndeterminacy {w : 𝒜.Cohomology} :
    w ∈ 𝒜.tripleMasseyIndeterminacy x z ↔
      ∃ s t : 𝒜.Cohomology, 𝒜.cohomologyGrading.koszulTwist 1 x * s + t * z = w := by
  simp [tripleMasseyIndeterminacy, Submodule.mem_sup]

/-- On a homogeneous class `x` the Koszul twist is a sign, so the indeterminacy of `⟨x, y, z⟩` is
the classical `x · H + H · z`. -/
theorem tripleMasseyIndeterminacy_eq_of_mem_piece {p : ℤ}
    (hx : x ∈ 𝒜.cohomologyGrading.piece p) :
    𝒜.tripleMasseyIndeterminacy x z =
      LinearMap.range (LinearMap.mulLeft R x) ⊔ LinearMap.range (LinearMap.mulRight R z) := by
  have hε : (((p.negOnePow : ℤ) : R)) * ((p.negOnePow : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [tripleMasseyIndeterminacy, 𝒜.cohomologyGrading.koszulTwist_one_apply_of_mem hx]
  congr 1
  -- Multiplying `x` by the sign `ε = (-1)^p`, with `ε² = 1`, does not change `x · H`.
  apply le_antisymm <;> rintro _ ⟨s, rfl⟩
  · refine ⟨((p.negOnePow : ℤ) : R) • s, ?_⟩
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, smul_mul_assoc, mul_smul_comm]
  · refine ⟨((p.negOnePow : ℤ) : R) • s, ?_⟩
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, smul_mul_assoc, mul_smul_comm,
      smul_smul, hε, one_smul]

/-! ### Definedness -/

/-- A defining system for `⟨x, y, z⟩` exists exactly when `x y = 0` and `y z = 0`. -/
theorem nonempty_tripleMasseyDefiningSystem_iff :
    Nonempty (𝒜.TripleMasseyDefiningSystem x y z) ↔ x * y = 0 ∧ y * z = 0 := by
  constructor
  · rintro ⟨⟨a, b, c, u, v, ha, hb, hc, rfl, rfl, rfl, hu, hv⟩⟩
    rw [cohomology_mul_eq_cohomologyMul, cohomology_mul_eq_cohomologyMul,
      cohomologyMul_cohomologyClass, cohomologyMul_cohomologyClass, cohomologyClass_eq_zero_iff,
      cohomologyClass_eq_zero_iff, mem_boundaries, mem_boundaries]
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  · rintro ⟨hxy, hyz⟩
    obtain ⟨a, ha, rfl⟩ := 𝒜.exists_cohomologyClass_eq x
    obtain ⟨b, hb, rfl⟩ := 𝒜.exists_cohomologyClass_eq y
    obtain ⟨c, hc, rfl⟩ := 𝒜.exists_cohomologyClass_eq z
    rw [cohomology_mul_eq_cohomologyMul, cohomologyMul_cohomologyClass,
      cohomologyClass_eq_zero_iff, mem_boundaries] at hxy hyz
    obtain ⟨u, hu⟩ := hxy
    obtain ⟨v, hv⟩ := hyz
    exact ⟨⟨a, b, c, u, v, ha, hb, hc, rfl, rfl, rfl, hu, hv⟩⟩

/-- The triple Massey product `⟨x, y, z⟩` is nonempty exactly when `x y = 0` and `y z = 0`. -/
theorem tripleMasseyProduct_nonempty_iff :
    (𝒜.tripleMasseyProduct x y z).Nonempty ↔ x * y = 0 ∧ y * z = 0 := by
  rw [tripleMasseyProduct, Set.range_nonempty_iff_nonempty,
    nonempty_tripleMasseyDefiningSystem_iff]

/-! ### The indeterminacy -/

/-- **The Massey product is stable under its indeterminacy**: changing the bounding cochains `u`
and `v` of a defining system by cycles adds an element of `τx · H + H · z` to its value. -/
theorem add_mem_tripleMasseyProduct {w i : 𝒜.Cohomology} (hw : w ∈ 𝒜.tripleMasseyProduct x y z)
    (hi : i ∈ 𝒜.tripleMasseyIndeterminacy x z) : w + i ∈ 𝒜.tripleMasseyProduct x y z := by
  obtain ⟨S, rfl⟩ := hw
  obtain ⟨s, t, rfl⟩ := mem_tripleMasseyIndeterminacy.mp hi
  obtain ⟨σ, hσ, rfl⟩ := 𝒜.exists_cohomologyClass_eq s
  obtain ⟨θ, hθ, rfl⟩ := 𝒜.exists_cohomologyClass_eq t
  rw [mem_cycles] at hσ hθ
  let T : 𝒜.TripleMasseyDefiningSystem x y z :=
    { S with
      u := S.u + θ
      v := S.v - σ
      m_one_u := by
        rw [← differential_apply, map_add, differential_apply, differential_apply, S.m_one_u,
          hθ, add_zero]
      m_one_v := by
        rw [← differential_apply, map_sub, differential_apply, differential_apply, S.m_one_v,
          hσ, sub_zero] }
  refine ⟨T, ?_⟩
  rw [TripleMasseyDefiningSystem.value_def, TripleMasseyDefiningSystem.value_def,
    𝒜.cohomologyClass_eq_add_add S.cycle_mem_cycles
      (𝒜.m_two_mem_cycles (𝒜.koszulTwist_mem_cycles S.a_mem_cycles) (𝒜.mem_cycles.mpr hσ))
      (𝒜.m_two_mem_cycles (𝒜.mem_cycles.mpr hθ) S.c_mem_cycles) T.cycle_mem_cycles ?_,
    ← 𝒜.cohomologyMul_cohomologyClass (𝒜.koszulTwist_mem_cycles S.a_mem_cycles)
      (𝒜.mem_cycles.mpr hσ),
    ← 𝒜.cohomologyMul_cohomologyClass (𝒜.mem_cycles.mpr hθ) S.c_mem_cycles,
    ← 𝒜.koszulTwist_cohomologyClass S.a_mem_cycles, S.cohomologyClass_a, S.cohomologyClass_c,
    cohomology_mul_eq_cohomologyMul, cohomology_mul_eq_cohomologyMul]
  simp only [TripleMasseyDefiningSystem.cycle_def, T, ← mul_apply, map_add, map_sub,
    LinearMap.add_apply]
  abel

namespace TripleMasseyDefiningSystem

variable (S : 𝒜.TripleMasseyDefiningSystem x y z)

/-- Changing the representative of `x` by a boundary does not change the value of a defining
system: if `a' = a + m₁ α`, then replacing `u` by `u + m₂ (α, b)` changes the Massey cycle by the
boundary of `m₂ (τα, v) - m₃ (α, b, c)`. -/
private theorem exists_a_eq {a' : A} (ha' : a' ∈ 𝒜.cycles) (hx : 𝒜.cohomologyClass ha' = x) :
    ∃ T : 𝒜.TripleMasseyDefiningSystem x y z,
      T.a = a' ∧ T.b = S.b ∧ T.c = S.c ∧ T.value = S.value := by
  have h := hx.trans S.cohomologyClass_a.symm
  rw [cohomologyClass_eq_iff, mem_boundaries] at h
  obtain ⟨α, hα⟩ := h
  obtain rfl : a' = S.a + 𝒜.m 1 ![α] := by rw [hα, add_sub_cancel]
  have hb := 𝒜.mem_cycles.mp S.b_mem_cycles
  have hc := 𝒜.mem_cycles.mp S.c_mem_cycles
  let T : 𝒜.TripleMasseyDefiningSystem x y z :=
    { S with
      a := S.a + 𝒜.m 1 ![α]
      u := S.u + 𝒜.m 2 ![α, S.b]
      a_mem_cycles := ha'
      cohomologyClass_a := hx
      m_one_u := by
        rw [← differential_apply, map_add, differential_apply, differential_apply, S.m_one_u,
          m_one_m_two, hb]
        simp only [← mul_apply, map_add, LinearMap.add_apply, map_zero, add_zero] }
  refine ⟨T, rfl, rfl, rfl, ?_⟩
  rw [value_def, value_def, cohomologyClass_eq_iff, mem_boundaries]
  refine ⟨𝒜.m 2 ![𝒜.grading.koszulTwist 1 α, S.v] - 𝒜.m 3 ![α, S.b, S.c], ?_⟩
  rw [← differential_apply, map_sub, differential_apply, differential_apply]
  simp only [cycle_def, T, m_one_m_two, m_one_m_three, m_one_koszulTwist,
    InternalGrading.koszulTwist_koszulTwist, S.m_one_v, hb, hc, m_three_zero₁, m_three_zero₂,
    m_three_add₀]
  simp only [← mul_apply, map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply]
  abel

/-- Changing the representative of `y` by a boundary does not change the value of a defining
system: if `b' = b + m₁ β`, then replacing `u` by `u + m₂ (τa, β)` and `v` by `v + m₂ (β, c)`
changes the Massey cycle by the boundary of `-m₃ (τa, β, c)`. -/
private theorem exists_b_eq {b' : A} (hb' : b' ∈ 𝒜.cycles) (hy : 𝒜.cohomologyClass hb' = y) :
    ∃ T : 𝒜.TripleMasseyDefiningSystem x y z,
      T.a = S.a ∧ T.b = b' ∧ T.c = S.c ∧ T.value = S.value := by
  have h := hy.trans S.cohomologyClass_b.symm
  rw [cohomologyClass_eq_iff, mem_boundaries] at h
  obtain ⟨β, hβ⟩ := h
  obtain rfl : b' = S.b + 𝒜.m 1 ![β] := by rw [hβ, add_sub_cancel]
  have ha := 𝒜.mem_cycles.mp S.a_mem_cycles
  have hc := 𝒜.mem_cycles.mp S.c_mem_cycles
  let T : 𝒜.TripleMasseyDefiningSystem x y z :=
    { S with
      b := S.b + 𝒜.m 1 ![β]
      u := S.u + 𝒜.m 2 ![𝒜.grading.koszulTwist 1 S.a, β]
      v := S.v + 𝒜.m 2 ![β, S.c]
      b_mem_cycles := hb'
      cohomologyClass_b := hy
      m_one_u := by
        rw [← differential_apply, map_add, differential_apply, differential_apply, S.m_one_u,
          m_one_m_two, m_one_koszulTwist, ha, InternalGrading.koszulTwist_koszulTwist]
        simp only [← mul_apply, map_add, map_zero, LinearMap.zero_apply, neg_zero, zero_add]
      m_one_v := by
        rw [← differential_apply, map_add, differential_apply, differential_apply, S.m_one_v,
          m_one_m_two, hc]
        simp only [← mul_apply, map_add, LinearMap.add_apply, map_zero, add_zero] }
  refine ⟨T, rfl, rfl, rfl, ?_⟩
  rw [value_def, value_def, cohomologyClass_eq_iff, mem_boundaries]
  refine ⟨-𝒜.m 3 ![𝒜.grading.koszulTwist 1 S.a, β, S.c], ?_⟩
  rw [← differential_apply, map_neg, differential_apply]
  simp only [cycle_def, T, m_one_m_three, m_one_koszulTwist,
    InternalGrading.koszulTwist_koszulTwist, ha, hc, map_zero, neg_zero, m_three_zero₀,
    m_three_zero₂, m_three_add₁]
  simp only [← mul_apply, map_add, LinearMap.add_apply]
  abel

/-- Changing the representative of `z` by a boundary does not change the value of a defining
system: if `c' = c + m₁ γ`, then replacing `v` by `v + m₂ (τb, γ)` changes the Massey cycle by the
boundary of `m₂ (τu, γ) - m₃ (τa, τb, γ)`. -/
private theorem exists_c_eq {c' : A} (hc' : c' ∈ 𝒜.cycles) (hz : 𝒜.cohomologyClass hc' = z) :
    ∃ T : 𝒜.TripleMasseyDefiningSystem x y z,
      T.a = S.a ∧ T.b = S.b ∧ T.c = c' ∧ T.value = S.value := by
  have h := hz.trans S.cohomologyClass_c.symm
  rw [cohomologyClass_eq_iff, mem_boundaries] at h
  obtain ⟨γ, hγ⟩ := h
  obtain rfl : c' = S.c + 𝒜.m 1 ![γ] := by rw [hγ, add_sub_cancel]
  have ha := 𝒜.mem_cycles.mp S.a_mem_cycles
  have hb := 𝒜.mem_cycles.mp S.b_mem_cycles
  let T : 𝒜.TripleMasseyDefiningSystem x y z :=
    { S with
      c := S.c + 𝒜.m 1 ![γ]
      v := S.v + 𝒜.m 2 ![𝒜.grading.koszulTwist 1 S.b, γ]
      c_mem_cycles := hc'
      cohomologyClass_c := hz
      m_one_v := by
        rw [← differential_apply, map_add, differential_apply, differential_apply, S.m_one_v,
          m_one_m_two, m_one_koszulTwist, hb, InternalGrading.koszulTwist_koszulTwist]
        simp only [← mul_apply, map_add, map_zero, LinearMap.zero_apply, neg_zero, zero_add] }
  refine ⟨T, rfl, rfl, rfl, ?_⟩
  rw [value_def, value_def, cohomologyClass_eq_iff, mem_boundaries]
  refine ⟨𝒜.m 2 ![𝒜.grading.koszulTwist 1 S.u, γ] -
    𝒜.m 3 ![𝒜.grading.koszulTwist 1 S.a, 𝒜.grading.koszulTwist 1 S.b, γ], ?_⟩
  rw [← differential_apply, map_sub, differential_apply, differential_apply]
  simp only [cycle_def, T, m_one_m_two, m_one_m_three, m_one_koszulTwist,
    InternalGrading.koszulTwist_koszulTwist, S.m_one_u, koszulTwist_m_two, ha, hb, map_zero,
    neg_zero, m_three_zero₀, m_three_zero₁, m_three_add₂]
  simp only [← mul_apply, map_add, map_neg, LinearMap.neg_apply]
  abel

/-- Two defining systems with the same representatives `a`, `b`, `c` have values differing by an
element of the indeterminacy: their bounding cochains differ by cycles. -/
private theorem value_sub_value_mem (S' : 𝒜.TripleMasseyDefiningSystem x y z) (ha : S'.a = S.a)
    (hb : S'.b = S.b) (hc : S'.c = S.c) :
    S'.value - S.value ∈ 𝒜.tripleMasseyIndeterminacy x z := by
  obtain ⟨a, b, c, u, v, ha₀, hb₀, hc₀, rfl, rfl, rfl, hu₀, hv₀⟩ := S
  obtain ⟨a', b', c', u', v', ha', hb', hc', hx, hy, hz, hu', hv'⟩ := S'
  dsimp only at ha hb hc
  subst ha hb hc
  have hu : 𝒜.m 1 ![u' - u] = 0 := by
    rw [← differential_apply, map_sub, differential_apply, differential_apply, hu', hu₀,
      sub_self]
  have hv : 𝒜.m 1 ![v - v'] = 0 := by
    rw [← differential_apply, map_sub, differential_apply, differential_apply, hv', hv₀,
      sub_self]
  rw [mem_tripleMasseyIndeterminacy]
  refine ⟨𝒜.cohomologyClass (𝒜.mem_cycles.mpr hv), 𝒜.cohomologyClass (𝒜.mem_cycles.mpr hu), ?_⟩
  rw [eq_sub_iff_add_eq', value_def, value_def, koszulTwist_cohomologyClass,
    cohomology_mul_eq_cohomologyMul, cohomology_mul_eq_cohomologyMul,
    cohomologyMul_cohomologyClass, cohomologyMul_cohomologyClass, ← cohomologyClass_eq_add_add]
  simp only [cycle_def, ← mul_apply, map_sub, LinearMap.sub_apply]
  abel

end TripleMasseyDefiningSystem

/-- **Two elements of the Massey product differ by an element of the indeterminacy.**  Any two
defining systems are connected by changing the representatives of `x`, `y`, `z` by boundaries,
which does not change the value, and then changing the bounding cochains by cycles. -/
theorem sub_mem_tripleMasseyIndeterminacy {w w' : 𝒜.Cohomology}
    (hw : w ∈ 𝒜.tripleMasseyProduct x y z) (hw' : w' ∈ 𝒜.tripleMasseyProduct x y z) :
    w' - w ∈ 𝒜.tripleMasseyIndeterminacy x z := by
  obtain ⟨S, rfl⟩ := hw
  obtain ⟨S', rfl⟩ := hw'
  obtain ⟨T₁, ha₁, hb₁, hc₁, hv₁⟩ := S.exists_a_eq S'.a_mem_cycles S'.cohomologyClass_a
  obtain ⟨T₂, ha₂, hb₂, hc₂, hv₂⟩ := T₁.exists_b_eq S'.b_mem_cycles S'.cohomologyClass_b
  obtain ⟨T₃, ha₃, hb₃, hc₃, hv₃⟩ := T₂.exists_c_eq S'.c_mem_cycles S'.cohomologyClass_c
  rw [← hv₁, ← hv₂, ← hv₃]
  exact T₃.value_sub_value_mem S' (by rw [ha₃, ha₂, ha₁]) (by rw [hb₃, hb₂])
    (by rw [hc₃])

/-- **The triple Massey product is a coset of its indeterminacy**: given one element `w` of
`⟨x, y, z⟩`, an element `w'` lies in `⟨x, y, z⟩` exactly when `w' - w` lies in `τx · H + H · z`. -/
theorem mem_tripleMasseyProduct_iff_sub_mem {w w' : 𝒜.Cohomology}
    (hw : w ∈ 𝒜.tripleMasseyProduct x y z) :
    w' ∈ 𝒜.tripleMasseyProduct x y z ↔ w' - w ∈ 𝒜.tripleMasseyIndeterminacy x z :=
  ⟨sub_mem_tripleMasseyIndeterminacy hw, fun h ↦ by
    simpa using add_mem_tripleMasseyProduct hw h⟩

end TauCeti.AInfinityAlgebra
