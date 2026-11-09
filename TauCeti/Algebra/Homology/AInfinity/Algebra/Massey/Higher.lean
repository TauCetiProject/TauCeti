/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Cohomology
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Massey
public import TauCeti.LinearAlgebra.TensorCoalgebra.BlockWord

/-!
# Higher Massey products of A-infinity algebras

Let `x₀, …, x_{n+1}` be cohomology classes of an `A∞` algebra `A`.  A *defining system* for their
Massey product assigns to every proper block `[a, a + b)` of the positions `0, …, n + 1`, that is
every block other than the whole interval, an entry `e a b ∈ A`, such that the entries `e i 1` of
the blocks of length one are cycles representing the classes `x i`, and such that on every proper
block of length at least two the defining equation

`∑ b_k (e c₀ (c₁ - c₀), e c₁ (c₂ - c₁), …) = 0`

holds, the sum running over all ways `a = c₀ < c₁ < ⋯ < c_k = a + b` of cutting the block into
consecutive sub-blocks, with `b_k` the suspended Taylor component of `A` in arity `k`.  The same
sum over the cuttings of the whole interval into at least two sub-blocks is the **Massey cycle**
of the defining system, and the **Massey product** `⟨x₀, …, x_{n+1}⟩` is the set of the classes of
the Massey cycles of all defining systems.  The entries are required to vanish away from the proper
blocks, so that a defining system is determined by its entries on them
(`TauCeti.AInfinityAlgebra.MasseyDefiningSystem.ext`).

The sum over cuttings is the suspended Taylor map applied to the block word of the entries,
`TauCeti.ReducedTensorWords.blockWord`.  The equations are stated with the suspended Taylor map,
which is the stored `A∞` structure; unsuspended, the arity-`k` term is `m_k` with the Koszul
twists of `TauCeti.AInfinityAlgebra.taylor_of_tprod`.  On a block of length two the defining
equation reads `m₁ (e a 2) + m₂ (τ (e a 1), e (a + 1) 1) = 0` (`taylor_blockWord_two`), with `τ`
the degree-one Koszul twist.

The block words of the entries deconcatenate like the blocks of a single word, so the co-Leibniz
rule controls the bar differential on them: the defining equations say that it vanishes on the
block words of the proper blocks, and it sends the block word of the whole interval to the single
letter given by the Massey cycle.  Since the bar differential squares to zero, the Massey cycle
is a cycle (`TauCeti.AInfinityAlgebra.MasseyDefiningSystem.cycle_mem_cycles`).  No sign
computation is needed: all signs are carried by the suspension.

For two classes the Massey product is the single class `τx · y` (`masseyProduct_two`).  For
three classes it is the triple Massey product `TauCeti.AInfinityAlgebra.tripleMasseyProduct`
after twisting the middle class (`masseyProduct_three`): the entry of the middle block is the
Koszul twist of the representative used there.  On homogeneous classes the Koszul twists are
signs, so for two and three classes the suspended convention used here agrees with the classical
products up to sign.

The higher operations of an `A∞` algebra produce defining systems.  Let `f : H → A` be an `A∞`
morphism and let `y₀, …, y_{n+1} ∈ H` be elements on whose proper blocks the suspended Taylor map of
`H` vanishes; in particular they are cycles.  The images under the bar map of `f` of the blocks of
the word `y₀ ⋯ y_{n+1}` are the block words of the Taylor components of `f` on these blocks, so
the components on the proper blocks form a defining system for the classes of the `f₁ (y i)`,
whose Massey cycle is cohomologous to `f₁ (b_{n+2} (y₀, …, y_{n+1}))`
(`TauCeti.AInfinityHom.cohomologyClass_mem_masseyProduct`).  For the inclusion of a minimal model
this says that the higher operations of the minimal model select elements of the higher Massey
products; that consequence lives in `TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Massey`.

## Main definitions

* `TauCeti.AInfinityAlgebra.MasseyDefiningSystem`: a defining system for the Massey product of
  `n + 2` classes.
* `TauCeti.AInfinityAlgebra.MasseyDefiningSystem.cycle`: its Massey cycle.
* `TauCeti.AInfinityAlgebra.MasseyDefiningSystem.value`: the class of its Massey cycle.
* `TauCeti.AInfinityAlgebra.masseyProduct`: the Massey product `⟨x₀, …, x_{n+1}⟩`.

## Main results

* `TauCeti.AInfinityAlgebra.taylor_mem_cycles_of_isBlockFamily`: if the suspended Taylor map
  vanishes on the proper sub-blocks of a block of a block family, its value on the block is a
  cycle.
* `TauCeti.AInfinityAlgebra.MasseyDefiningSystem.barDifferential_blockWord`: the bar differential
  sends the block word of the whole interval to the Massey cycle.
* `TauCeti.AInfinityAlgebra.MasseyDefiningSystem.cycle_mem_cycles`: the Massey cycle is a cycle.
* `TauCeti.AInfinityAlgebra.masseyProduct_two`: the Massey product of two classes is `τx · y`.
* `TauCeti.AInfinityAlgebra.masseyProduct_three`: the Massey product of three classes is a triple
  Massey product.
* `TauCeti.AInfinityHom.cohomologyClass_mem_masseyProduct`: an `A∞` morphism carries the higher
  operations on elements with vanishing lower operations into the Massey product of their images.

## References

* J. P. May, *Matric Massey products*, J. Algebra 12 (1969), 533--568, Section 1.
* D.-M. Lu, J. H. Palmieri, Q.-S. Wu, J. J. Zhang, *A-infinity structure on Ext-algebras*,
  J. Pure Appl. Algebra 213 (2009), Section 3 and Theorem 3.1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.3.
-/

public section

namespace TauCeti

open ReducedTensorWords

universe uR uA uH

variable {R : Type uR} {A : Type uA} {H : Type uH} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup H] [Module R H]

namespace AInfinityAlgebra

variable (𝒜 : AInfinityAlgebra R A)

/-! ### The bar differential on block families -/

/-- On the block word of a block of length two, the suspended Taylor map is
`m₁ (e a 2) + m₂ (τ (e a 1), e (a + 1) 1)`, with `τ` the degree-one Koszul twist. -/
theorem taylor_blockWord_two (e : ℕ → ℕ → A) (a : ℕ) :
    𝒜.taylor (blockWord R e a 2) =
      𝒜.m 1 ![e a 2] + 𝒜.m 2 ![𝒜.grading.koszulTwist 1 (e a 1), e (a + 1) 1] := by
  rw [blockWord_two, map_add, taylor_ofLetter, prepend_ofLetter, taylor_of_two]

variable {𝒜} {V : ℕ → ℕ → ReducedTensorWords R A}

/-- If the suspended Taylor map vanishes on every sub-block of a nonempty block of a block
family, then so does the bar differential. -/
theorem barDifferential_eq_zero_of_isBlockFamily (hV : IsBlockFamily R V) {a b : ℕ} (hb : 0 < b)
    (h : ∀ c k, 0 < k → a ≤ c → c + k ≤ a + b → 𝒜.taylor (V c k) = 0) :
    𝒜.barDifferential (V a b) = 0 :=
  𝒜.isGradedCoderivation_barDifferential.apply_eq_zero_of_isBlockFamily hV hb
    fun c k hk h₁ h₂ ↦ by
      rw [← LinearMap.comp_apply, letter_comp_barDifferential]
      exact h c k hk h₁ h₂

/-- If the suspended Taylor map vanishes on every proper sub-block of a block of a block family,
then the bar differential sends that block to the single letter given by the Taylor map. -/
theorem barDifferential_eq_ofLetter_of_isBlockFamily (hV : IsBlockFamily R V) {a b : ℕ}
    (h : ∀ c k, 0 < k → k < b → a ≤ c → c + k ≤ a + b → 𝒜.taylor (V c k) = 0) :
    𝒜.barDifferential (V a b) = ofLetter R A (𝒜.taylor (V a b)) := by
  rw [𝒜.isGradedCoderivation_barDifferential.apply_eq_ofLetter_of_isBlockFamily hV
    fun c k hk hkn h₁ h₂ ↦ by
      rw [← LinearMap.comp_apply, letter_comp_barDifferential]
      exact h c k hk hkn h₁ h₂,
    ← LinearMap.comp_apply (letter R A), letter_comp_barDifferential]

/-- **Vanishing on proper sub-blocks makes the Taylor map a cycle**: if the suspended Taylor map
vanishes on every proper sub-block of a block of a block family, then its value on the block is a
cycle. -/
theorem taylor_mem_cycles_of_isBlockFamily (hV : IsBlockFamily R V) {a b : ℕ}
    (h : ∀ c k, 0 < k → k < b → a ≤ c → c + k ≤ a + b → 𝒜.taylor (V c k) = 0) :
    𝒜.taylor (V a b) ∈ 𝒜.cycles := by
  have hd := congrArg 𝒜.barDifferential (barDifferential_eq_ofLetter_of_isBlockFamily hV h)
  rw [← LinearMap.comp_apply 𝒜.barDifferential 𝒜.barDifferential, barDifferential_sq,
    LinearMap.zero_apply, barDifferential_ofLetter] at hd
  rw [mem_cycles]
  simpa using congrArg (letter R A) hd.symm

/-- If the suspended Taylor map vanishes on every proper block of the word `y₀ ⋯ y_{n+1}`, then
its value on the whole word is a cycle. -/
theorem taylor_subword_mem_cycles {n : ℕ} {y : Fin (n + 2) → A}
    (hy : ∀ a b, 0 < b → b ≤ n + 1 → a + b ≤ n + 2 → 𝒜.taylor (subword R y a b) = 0) :
    𝒜.taylor (subword R y 0 (n + 2)) ∈ 𝒜.cycles :=
  taylor_mem_cycles_of_isBlockFamily (isBlockFamily_subword y)
    fun c k hk _ _ h₂ ↦ hy c k hk (by omega) (by omega)

/-- If the suspended Taylor map vanishes on every proper block of the word `y₀ ⋯ y_{n+1}`, then
every letter `y i` is a cycle. -/
theorem mem_cycles_of_taylor_subword_eq_zero {n : ℕ} {y : Fin (n + 2) → A}
    (hy : ∀ a b, 0 < b → b ≤ n + 1 → a + b ≤ n + 2 → 𝒜.taylor (subword R y a b) = 0)
    (i : Fin (n + 2)) : y i ∈ 𝒜.cycles := by
  have h := hy i 1 one_pos (by omega) (by omega)
  rwa [subword_one R A y i.isLt, Fin.eta, taylor_ofLetter, ← mem_cycles] at h

variable (𝒜)

/-! ### Defining systems and Massey cycles -/

/-- A **defining system** for the Massey product `⟨x₀, …, x_{n+1}⟩`: an entry `entry a b` for every
proper block `[a, a + b)` of the positions `0, …, n + 1`, vanishing away from those blocks, such
that the entries of the blocks of length one are cycles representing the classes `x i`, and such
that the suspended Taylor map vanishes on the block word of the entries of every proper block of
length at least two. -/
structure MasseyDefiningSystem {n : ℕ} (x : Fin (n + 2) → 𝒜.Cohomology) where
  /-- The entry of the block `[a, a + b)`. -/
  entry : ℕ → ℕ → A
  /-- The entries vanish away from the proper blocks. -/
  entry_eq_zero : ∀ a b, ¬(0 < b ∧ b ≤ n + 1 ∧ a + b ≤ n + 2) → entry a b = 0
  /-- The entries of the blocks of length one are cycles. -/
  entry_mem_cycles : ∀ i : Fin (n + 2), entry i 1 ∈ 𝒜.cycles
  /-- The entry of the block `[i, i + 1)` represents `x i`. -/
  cohomologyClass_entry : ∀ i, 𝒜.cohomologyClass (entry_mem_cycles i) = x i
  /-- The defining equations on the proper blocks of length at least two. -/
  taylor_blockWord : ∀ a b, 2 ≤ b → b ≤ n + 1 → a + b ≤ n + 2 →
    𝒜.taylor (blockWord R entry a b) = 0

namespace MasseyDefiningSystem

variable {𝒜} {n : ℕ} {x : Fin (n + 2) → 𝒜.Cohomology} (S : 𝒜.MasseyDefiningSystem x)

/-- A defining system is determined by its entries on the proper blocks. -/
@[ext]
theorem ext {S T : 𝒜.MasseyDefiningSystem x}
    (h : ∀ a b, 0 < b → b ≤ n + 1 → a + b ≤ n + 2 → S.entry a b = T.entry a b) : S = T := by
  have he : S.entry = T.entry := funext fun a ↦ funext fun b ↦ by
    by_cases hab : 0 < b ∧ b ≤ n + 1 ∧ a + b ≤ n + 2
    · exact h a b hab.1 hab.2.1 hab.2.2
    · rw [S.entry_eq_zero a b hab, T.entry_eq_zero a b hab]
  cases S
  cases T
  subst he
  rfl

/-- The suspended Taylor map vanishes on the block word of every proper block, including the
blocks of length one. -/
theorem taylor_blockWord_eq_zero {a b : ℕ} (hb : 0 < b) (hbn : b ≤ n + 1) (hab : a + b ≤ n + 2) :
    𝒜.taylor (blockWord R S.entry a b) = 0 := by
  rcases Nat.lt_or_ge b 2 with h | h
  · obtain rfl : b = 1 := by omega
    rw [blockWord_one, taylor_ofLetter, ← mem_cycles]
    exact S.entry_mem_cycles ⟨a, by omega⟩
  · exact S.taylor_blockWord a b h hbn hab

/-- The **Massey cycle** of a defining system: the suspended Taylor map on the block word of the
whole interval, the sum over all cuttings of the interval into at least two blocks. -/
noncomputable def cycle : A :=
  𝒜.taylor (blockWord R S.entry 0 (n + 2))

/-- The Massey cycle, unfolded. -/
theorem cycle_def : S.cycle = 𝒜.taylor (blockWord R S.entry 0 (n + 2)) := (rfl)

/-- The Massey cycle as the sum over the length `c + 1` of the first block of a cutting of the
interval into at least two blocks. -/
theorem cycle_eq_sum : S.cycle = ∑ c ∈ Finset.range (n + 1),
    𝒜.taylor (prepend R A (S.entry 0 (c + 1)) (blockWord R S.entry (c + 1) (n + 1 - c))) := by
  rw [cycle_def, blockWord_succ,
    S.entry_eq_zero 0 (n + 1 + 1) (by omega), map_zero, zero_add, map_sum]
  simp only [zero_add]

/-- The bar differential sends the block word of the whole interval to the single letter given by
the Massey cycle. -/
theorem barDifferential_blockWord :
    𝒜.barDifferential (blockWord R S.entry 0 (n + 2)) = ofLetter R A S.cycle :=
  barDifferential_eq_ofLetter_of_isBlockFamily (isBlockFamily_blockWord S.entry)
    fun _ _ hk _ _ h₂ ↦ S.taylor_blockWord_eq_zero hk (by omega) (by omega)

/-- **The Massey cycle of a defining system is a cycle.** -/
theorem cycle_mem_cycles : S.cycle ∈ 𝒜.cycles :=
  taylor_mem_cycles_of_isBlockFamily (isBlockFamily_blockWord S.entry)
    fun _ _ hk _ _ h₂ ↦ S.taylor_blockWord_eq_zero hk (by omega) (by omega)

/-- The class of the Massey cycle of a defining system: an element of the Massey product. -/
noncomputable def value : 𝒜.Cohomology :=
  𝒜.cohomologyClass S.cycle_mem_cycles

/-- The value of a defining system is the class of its Massey cycle. -/
theorem value_def : S.value = 𝒜.cohomologyClass S.cycle_mem_cycles := (rfl)

end MasseyDefiningSystem

/-! ### Massey products -/

/-- The **Massey product** `⟨x₀, …, x_{n+1}⟩`: the set of the classes of the Massey cycles of all
defining systems.  It is empty when no defining system exists. -/
noncomputable def masseyProduct {n : ℕ} (x : Fin (n + 2) → 𝒜.Cohomology) : Set 𝒜.Cohomology :=
  Set.range (MasseyDefiningSystem.value (𝒜 := 𝒜) (x := x))

variable {𝒜}

/-- An element of `⟨x₀, …, x_{n+1}⟩` is the value of some defining system. -/
theorem mem_masseyProduct {n : ℕ} {x : Fin (n + 2) → 𝒜.Cohomology} {w : 𝒜.Cohomology} :
    w ∈ 𝒜.masseyProduct x ↔ ∃ S : 𝒜.MasseyDefiningSystem x, S.value = w :=
  Iff.rfl

/-- The value of a defining system lies in the Massey product. -/
@[simp]
theorem MasseyDefiningSystem.value_mem {n : ℕ} {x : Fin (n + 2) → 𝒜.Cohomology}
    (S : 𝒜.MasseyDefiningSystem x) : S.value ∈ 𝒜.masseyProduct x :=
  ⟨S, rfl⟩

/-! ### Two and three classes -/

namespace MasseyDefiningSystem

/-- The Massey cycle of a defining system for two classes is `m₂ (τ e₀, e₁)`, with `e₀`, `e₁` the
representatives and `τ` the degree-one Koszul twist. -/
theorem cycle_two {x : Fin 2 → 𝒜.Cohomology} (S : 𝒜.MasseyDefiningSystem x) :
    S.cycle = 𝒜.m 2 ![𝒜.grading.koszulTwist 1 (S.entry 0 1), S.entry 1 1] := by
  simp only [cycle_eq_sum, zero_add, Finset.sum_range_one, Nat.sub_zero, blockWord_one,
    prepend_ofLetter, taylor_of_two]

/-- The value of a defining system for two classes `x`, `y` is `τx · y`. -/
theorem value_two {x : Fin 2 → 𝒜.Cohomology} (S : 𝒜.MasseyDefiningSystem x) :
    S.value = 𝒜.cohomologyGrading.koszulTwist 1 (x 0) * x 1 := by
  rw [value_def, ← S.cohomologyClass_entry 0, ← S.cohomologyClass_entry 1,
    koszulTwist_cohomologyClass, cohomology_mul_eq_cohomologyMul, cohomologyMul_cohomologyClass]
  exact 𝒜.cohomologyClass_congr _ _ S.cycle_two

/-- The Massey cycle of a defining system for three classes, with representatives `e₀ = e 0 1`,
`e₁ = e 1 1`, `e₂ = e 2 1` and bounding entries `e 0 2`, `e 1 2`:
`m₂ (τ e₀, e 1 2) + m₃ (e₀, τ e₁, e₂) + m₂ (τ (e 0 2), e₂)`. -/
theorem cycle_three {x : Fin 3 → 𝒜.Cohomology} (S : 𝒜.MasseyDefiningSystem x) :
    S.cycle = 𝒜.m 2 ![𝒜.grading.koszulTwist 1 (S.entry 0 1), S.entry 1 2] +
      𝒜.m 3 ![S.entry 0 1, 𝒜.grading.koszulTwist 1 (S.entry 1 1), S.entry 2 1] +
        𝒜.m 2 ![𝒜.grading.koszulTwist 1 (S.entry 0 2), S.entry 2 1] := by
  have h₃ : ∀ a b c : A, prepend R A a (prepend R A b (ofLetter R A c)) =
      of R A (3 : ℕ+) (PiTensorProduct.tprod R ![a, b, c]) := fun a b c ↦ by
    rw [prepend_ofLetter]
    exact prepend_of_tprod a (2 : ℕ+) ![b, c]
  simp only [cycle_eq_sum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd, Nat.reduceSub, blockWord_two, blockWord_one, map_add, h₃, taylor_of_three]
  simp only [prepend_ofLetter, taylor_of_two]

end MasseyDefiningSystem

/-- **The Massey product of two classes** is the single class `τx · y`, with `τ` the degree-one
Koszul twist. -/
theorem masseyProduct_two (x y : 𝒜.Cohomology) :
    𝒜.masseyProduct ![x, y] = {𝒜.cohomologyGrading.koszulTwist 1 x * y} := by
  ext w
  rw [Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨S, rfl⟩
    rw [S.value_two]
    rfl
  · rintro rfl
    obtain ⟨a, ha, rfl⟩ := 𝒜.exists_cohomologyClass_eq x
    obtain ⟨b, hb, rfl⟩ := 𝒜.exists_cohomologyClass_eq y
    -- The representatives are the only entries.
    let S : 𝒜.MasseyDefiningSystem ![𝒜.cohomologyClass ha, 𝒜.cohomologyClass hb] :=
      { entry := fun i k ↦ if k = 1 then (if i = 0 then a else if i = 1 then b else 0) else 0
        entry_eq_zero := fun i k h ↦ by
          split_ifs <;> first | rfl | exact absurd ⟨by omega, by omega, by omega⟩ h
        entry_mem_cycles := fun i ↦ by
          fin_cases i
          exacts [by simpa using ha, by simpa using hb]
        cohomologyClass_entry := fun i ↦ by
          fin_cases i
          exacts [𝒜.cohomologyClass_congr _ ha (by simp), 𝒜.cohomologyClass_congr _ hb (by simp)]
        taylor_blockWord := fun _ _ h₁ h₂ _ ↦ (by omega : False).elim }
    exact ⟨S, S.value_two⟩

/-- Every value of a defining system for `⟨x, y, z⟩` is the value of the triple defining system
for `x`, `τy`, `z` with representatives `e 0 1`, `τ (e 1 1)`, `e 2 1` and bounding cochains
`τ (e 0 2)` and `-e 1 2`. -/
private theorem masseyProduct_three_subset (x y z : 𝒜.Cohomology) :
    𝒜.masseyProduct ![x, y, z] ⊆
      𝒜.tripleMasseyProduct x (𝒜.cohomologyGrading.koszulTwist 1 y) z := by
  intro w hw
  obtain ⟨S, rfl⟩ := mem_masseyProduct.1 hw
  have h₀ := S.taylor_blockWord 0 2 le_rfl le_rfl (by omega)
  have h₁ := S.taylor_blockWord 1 2 le_rfl le_rfl (by omega)
  rw [taylor_blockWord_two] at h₀ h₁
  have hb := 𝒜.koszulTwist_mem_cycles (S.entry_mem_cycles 1)
  let T : 𝒜.TripleMasseyDefiningSystem x (𝒜.cohomologyGrading.koszulTwist 1 y) z :=
    { a := S.entry 0 1
      b := 𝒜.grading.koszulTwist 1 (S.entry 1 1)
      c := S.entry 2 1
      u := 𝒜.grading.koszulTwist 1 (S.entry 0 2)
      v := -S.entry 1 2
      a_mem_cycles := S.entry_mem_cycles 0
      b_mem_cycles := hb
      c_mem_cycles := S.entry_mem_cycles 2
      cohomologyClass_a := S.cohomologyClass_entry 0
      cohomologyClass_b := by
        rw [← koszulTwist_cohomologyClass 𝒜 (S.entry_mem_cycles 1), S.cohomologyClass_entry 1]
        rfl
      cohomologyClass_c := S.cohomologyClass_entry 2
      m_one_u := by
        rw [m_one_koszulTwist, eq_neg_of_add_eq_zero_left h₀, map_neg, neg_neg,
          koszulTwist_m_two, InternalGrading.koszulTwist_koszulTwist]
      m_one_v := by
        rw [← differential_apply, map_neg, differential_apply, eq_neg_of_add_eq_zero_left h₁,
          neg_neg] }
  refine mem_tripleMasseyProduct.2 ⟨T, ?_⟩
  rw [TripleMasseyDefiningSystem.value_def, MasseyDefiningSystem.value_def]
  refine 𝒜.cohomologyClass_congr _ _ ?_
  rw [TripleMasseyDefiningSystem.cycle_def, S.cycle_three]
  simp only [T, ← mul_apply, map_neg]
  abel

/-- Every value of a triple defining system for `x`, `τy`, `z` is the value of the defining
system for `⟨x, y, z⟩` with entries `a`, `τb`, `c` on the blocks of length one and `τu`, `-v` on
the blocks of length two. -/
private theorem tripleMasseyProduct_subset_masseyProduct_three (x y z : 𝒜.Cohomology) :
    𝒜.tripleMasseyProduct x (𝒜.cohomologyGrading.koszulTwist 1 y) z ⊆
      𝒜.masseyProduct ![x, y, z] := by
  intro w hw
  obtain ⟨T, rfl⟩ := mem_tripleMasseyProduct.1 hw
  -- The entries of the blocks `[0,1)`, `[1,2)`, `[2,3)`, `[0,2)`, `[1,3)`.
  let e : ℕ → ℕ → A := fun i k ↦
    if k = 1 then
      (if i = 0 then T.a else if i = 1 then 𝒜.grading.koszulTwist 1 T.b else
        if i = 2 then T.c else 0)
    else if k = 2 then (if i = 0 then 𝒜.grading.koszulTwist 1 T.u else if i = 1 then -T.v else 0)
    else 0
  have hb := 𝒜.koszulTwist_mem_cycles T.b_mem_cycles
  let S : 𝒜.MasseyDefiningSystem ![x, y, z] :=
    { entry := e
      entry_eq_zero := fun i k h ↦ by
        simp only [e]
        split_ifs <;> first | rfl | exact absurd ⟨by omega, by omega, by omega⟩ h
      entry_mem_cycles := fun i ↦ by
        fin_cases i
        exacts [by simpa [e] using T.a_mem_cycles, by simpa [e] using hb,
          by simpa [e] using T.c_mem_cycles]
      cohomologyClass_entry := fun i ↦ by
        fin_cases i
        · exact (𝒜.cohomologyClass_congr _ T.a_mem_cycles (by simp [e])).trans
            T.cohomologyClass_a
        · refine (𝒜.cohomologyClass_congr _ hb (by simp [e])).trans ?_
          rw [← koszulTwist_cohomologyClass 𝒜 T.b_mem_cycles, T.cohomologyClass_b,
            InternalGrading.koszulTwist_koszulTwist]
          rfl
        · exact (𝒜.cohomologyClass_congr _ T.c_mem_cycles (by simp [e])).trans
            T.cohomologyClass_c
      taylor_blockWord := fun i k h₁ h₂ h₃ ↦ by
        obtain rfl : k = 2 := by omega
        rw [taylor_blockWord_two]
        obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
        · simp only [e, ↓reduceIte, one_ne_zero, OfNat.ofNat_ne_one, zero_add,
            m_one_koszulTwist, T.m_one_u, koszulTwist_m_two, neg_add_cancel]
        · simp only [e, ↓reduceIte, OfNat.ofNat_ne_one, one_ne_zero,
            Nat.reduceAdd, OfNat.ofNat_ne_zero, InternalGrading.koszulTwist_koszulTwist]
          rw [← differential_apply, map_neg, differential_apply, T.m_one_v, neg_add_cancel] }
  refine mem_masseyProduct.2 ⟨S, ?_⟩
  rw [TripleMasseyDefiningSystem.value_def, MasseyDefiningSystem.value_def]
  refine 𝒜.cohomologyClass_congr _ _ ?_
  rw [TripleMasseyDefiningSystem.cycle_def, S.cycle_three]
  simp only [S, e, ↓reduceIte, one_ne_zero, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero,
    InternalGrading.koszulTwist_koszulTwist, ← mul_apply, map_neg]
  abel

/-- **The Massey product of three classes is a triple Massey product**: `⟨x, y, z⟩` in the sense of
defining systems on blocks is the triple Massey product of `x`, `τy`, `z`, with `τ` the degree-one
Koszul twist.  The entry of the middle block is the Koszul twist of the middle representative of a
triple defining system, and the entries `e 0 2`, `e 1 2` of the blocks of length two are the twist
of the first bounding cochain and the negative of the second.  On a homogeneous class `y` the twist
is the sign `(-1)^{|y|}`. -/
theorem masseyProduct_three (x y z : 𝒜.Cohomology) :
    𝒜.masseyProduct ![x, y, z] =
      𝒜.tripleMasseyProduct x (𝒜.cohomologyGrading.koszulTwist 1 y) z :=
  (masseyProduct_three_subset x y z).antisymm (tripleMasseyProduct_subset_masseyProduct_three x y z)

end AInfinityAlgebra

/-! ### Higher operations select elements of Massey products -/

namespace AInfinityHom

variable {ℋ : AInfinityAlgebra R H} {𝒜 : AInfinityAlgebra R A}

/-- **Higher operations encode defining systems.**  Let `f : H → A` be an `A∞` morphism and let
`y₀, …, y_{n+1}` be elements of `H` such that the suspended Taylor map of `H` vanishes on every
proper block `y_a ⋯ y_{a+b-1}` (in particular every `y i` is a cycle).  Then the class of
`f₁ (b_{n+2} (y₀, …, y_{n+1}))` lies in the Massey product of the classes of the `f₁ (y i)`.  The
defining system consists of the Taylor components of `f` on the proper blocks of `y₀ ⋯ y_{n+1}`. -/
theorem cohomologyClass_mem_masseyProduct (f : AInfinityHom ℋ 𝒜) {n : ℕ} {y : Fin (n + 2) → H}
    (hy : ∀ a b, 0 < b → b ≤ n + 1 → a + b ≤ n + 2 → ℋ.taylor (subword R y a b) = 0) :
    𝒜.cohomologyClass
        (f.linearPart_mem_cycles (AInfinityAlgebra.taylor_subword_mem_cycles hy)) ∈
      𝒜.masseyProduct fun i ↦ 𝒜.cohomologyClass
        (f.linearPart_mem_cycles (AInfinityAlgebra.mem_cycles_of_taylor_subword_eq_zero hy i)) := by
  have hx : ∀ i, f.linearPart (y i) ∈ 𝒜.cycles := fun i ↦
    f.linearPart_mem_cycles (AInfinityAlgebra.mem_cycles_of_taylor_subword_eq_zero hy i)
  -- The bar differential of `H` vanishes on the proper blocks of `y`, and sends the whole word to
  -- the single letter `b_{n+2} (y₀, …, y_{n+1})`.
  have hd₀ : ∀ a b, 0 < b → b ≤ n + 1 → a + b ≤ n + 2 →
      ℋ.barDifferential (subword R y a b) = 0 := fun a b hb hbn hab ↦
    AInfinityAlgebra.barDifferential_eq_zero_of_isBlockFamily (isBlockFamily_subword y) hb
      fun c k hk _ h₂ ↦ hy c k hk (by omega) (by omega)
  have hd : ℋ.barDifferential (subword R y 0 (n + 2)) =
      ofLetter R H (ℋ.taylor (subword R y 0 (n + 2))) :=
    AInfinityAlgebra.barDifferential_eq_ofLetter_of_isBlockFamily (isBlockFamily_subword y)
      fun c k hk _ _ h₂ ↦ hy c k hk (by omega) (by omega)
  -- The images of the blocks of `y` under the bar map of `f` are the block words of the Taylor
  -- components `e'` of `f` on these blocks.  The entries `e` are these components on the proper
  -- blocks.
  let e' : ℕ → ℕ → A := fun a b ↦ f.taylor (subword R y a b)
  let e : ℕ → ℕ → A := fun a b ↦ if 0 < b ∧ b ≤ n + 1 ∧ a + b ≤ n + 2 then e' a b else 0
  have hVe' : ∀ a b, 0 < b → f.barMap (subword R y a b) = blockWord R e' a b := fun a b hb ↦
    ((isBlockFamily_subword y).map f.isCoalgHom_barMap).eq_blockWord e' hb fun c k _ _ _ ↦ by
      rw [← LinearMap.comp_apply, ← taylor_def]
  have hVe : ∀ a b, 0 < b → b ≤ n + 1 → a + b ≤ n + 2 →
      f.barMap (subword R y a b) = blockWord R e a b := fun a b hb hbn hab ↦
    (hVe' a b hb).trans (blockWord_congr e' fun c k hk h₁ h₂ ↦
      (ite_eq_left ⟨hk, by omega, by omega⟩).symm)
  have he : ∀ i : Fin (n + 2), e i 1 = f.linearPart (y i) := fun i ↦ by
    have hi : 0 < 1 ∧ 1 ≤ n + 1 ∧ (i : ℕ) + 1 ≤ n + 2 := ⟨one_pos, by omega, by omega⟩
    simp only [e, e', ite_eq_left hi, subword_one R H y i.isLt, Fin.eta, linearPart_apply]
  let S : 𝒜.MasseyDefiningSystem fun i ↦ 𝒜.cohomologyClass (hx i) :=
    { entry := e
      entry_eq_zero := fun _ _ h ↦ ite_eq_right h
      entry_mem_cycles := fun i ↦ by
        rw [he]
        exact hx i
      cohomologyClass_entry := fun i ↦ 𝒜.cohomologyClass_congr _ _ (he i)
      taylor_blockWord := fun a b hb hbn hab ↦ by
        rw [← hVe a b (by omega) hbn hab, ← LinearMap.comp_apply, taylor_comp_barMap,
          LinearMap.comp_apply, hd₀ a b (by omega) hbn hab, map_zero] }
  refine ⟨S, ?_⟩
  -- The Massey cycle differs from `f₁ (b_{n+2} (y₀, …, y_{n+1}))` by a boundary.
  have hsplit := blockWord_add_ofLetter (R := R) e (e' := e') (a := 0) (b := n + 2) (by omega)
    fun c k hk hkn _ h₂ ↦ ite_eq_left ⟨hk, by omega, by omega⟩
  have he₀ : e 0 (n + 2) = 0 := ite_eq_right (by omega)
  rw [he₀, map_zero, add_zero,
    ← hVe' 0 (n + 2) (by omega)] at hsplit
  have hcycle :
      S.cycle = f.linearPart (ℋ.taylor (subword R y 0 (n + 2))) - 𝒜.m 1 ![e' 0 (n + 2)] := by
    rw [AInfinityAlgebra.MasseyDefiningSystem.cycle_def, eq_sub_of_add_eq hsplit, map_sub,
      AInfinityAlgebra.taylor_ofLetter, ← LinearMap.comp_apply 𝒜.taylor, taylor_comp_barMap,
      LinearMap.comp_apply, hd, ← linearPart_apply]
  rw [AInfinityAlgebra.MasseyDefiningSystem.value_def, AInfinityAlgebra.cohomologyClass_eq_iff,
    hcycle, sub_sub_cancel_left]
  exact 𝒜.boundaries.neg_mem ((AInfinityAlgebra.mem_boundaries 𝒜).2 ⟨_, rfl⟩)

end AInfinityHom

end TauCeti
