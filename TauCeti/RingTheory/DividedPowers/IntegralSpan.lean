/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowers.NormalOrdering
public import TauCeti.RingTheory.DividedPowers.Basis
public import Mathlib.Algebra.Algebra.Operations
import TauCeti.Algebra.Ring.Subgroup

/-!
# Adjoining divided powers in ordered form

For a subring `T` of a rational algebra and an element `x`, the ordered additive span consists
of integral combinations of `t x⁽ⁿ⁾`, with `t ∈ T`. To identify this span with the ring obtained
by adjoining the divided powers of `x`, it suffices to collect `x⁽ⁿ⁾ g` for generators `g` of
`T`. The collection criterion propagates through sums, negatives and products, without rational
division. This is useful when constructing integral normal forms one root at a time.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace Subring

open TauCeti.Associative

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Integral combinations of the ordered products `t x⁽ⁿ⁾`, with `t` in `T`. -/
noncomputable def dividedPowerExtensionSpan (T : Subring A) (x : A) : AddSubgroup A :=
  AddSubgroup.closure {a | ∃ t ∈ T, ∃ n : ℕ, t * dividedPower n x = a}

/-- Every ordered product belongs to the extension span. -/
theorem mul_dividedPower_mem_extensionSpan (T : Subring A) (x : A) {t : A}
    (ht : t ∈ T) (n : ℕ) : t * dividedPower n x ∈ dividedPowerExtensionSpan T x :=
  AddSubgroup.subset_closure ⟨t, ht, n, rfl⟩

/-- The universal property of the ordered extension span. -/
@[simp]
theorem dividedPowerExtensionSpan_le_iff {T : Subring A} {x : A} {S : AddSubgroup A} :
    dividedPowerExtensionSpan T x ≤ S ↔
      ∀ t ∈ T, ∀ n : ℕ, t * dividedPower n x ∈ S := by
  simp only [dividedPowerExtensionSpan, AddSubgroup.closure_le, Set.subset_def,
    Set.mem_ofPred_eq]
  constructor
  · intro h t ht n
    exact h _ ⟨t, ht, n, rfl⟩
  · rintro h _ ⟨t, ht, n, rfl⟩
    exact h t ht n

/-- Membership in the ordered extension span means being a finite integral combination of
products of coefficient-ring elements with divided powers. -/
theorem mem_dividedPowerExtensionSpan_iff {T : Subring A} {x a : A} :
    a ∈ dividedPowerExtensionSpan T x ↔
      ∃ c : (T × ℕ) →₀ ℤ,
        c.sum (fun i r => r • ((i.1 : A) * dividedPower i.2 x)) = a := by
  let p : T × ℕ → A := fun i => (i.1 : A) * dividedPower i.2 x
  have hspan : dividedPowerExtensionSpan T x =
      (Submodule.span ℤ (Set.range p)).toAddSubgroup := by
    apply le_antisymm
    · rw [dividedPowerExtensionSpan_le_iff]
      intro t ht n
      exact Submodule.subset_span ⟨(⟨t, ht⟩, n), rfl⟩
    · rw [← AddSubgroup.toIntSubmodule_toAddSubgroup (dividedPowerExtensionSpan T x),
        Submodule.toAddSubgroup_le, Submodule.span_le]
      rintro _ ⟨⟨t, n⟩, rfl⟩
      exact mul_dividedPower_mem_extensionSpan T x t.property n
  rw [hspan]
  exact Finsupp.mem_span_range_iff_exists_finsupp

/-- The coefficient ring is contained in the ordered extension span. -/
theorem mem_extensionSpan_of_mem {T : Subring A} {x t : A} (ht : t ∈ T) :
    t ∈ dividedPowerExtensionSpan T x := by
  simpa using mul_dividedPower_mem_extensionSpan T x ht 0

/-- Each divided power of the adjoined element belongs to the ordered extension span. -/
@[simp]
theorem dividedPower_mem_extensionSpan (T : Subring A) (x : A) (n : ℕ) :
    dividedPower n x ∈ dividedPowerExtensionSpan T x := by
  simpa using mul_dividedPower_mem_extensionSpan T x T.one_mem n

/-- The ordered extension span is a left module over its coefficient ring. -/
theorem mul_mem_extensionSpan_of_mem {T : Subring A} {x t a : A} (ht : t ∈ T)
    (ha : a ∈ dividedPowerExtensionSpan T x) : t * a ∈ dividedPowerExtensionSpan T x := by
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
      obtain ⟨u, hu, n, rfl⟩ := ha
      simpa only [← mul_assoc] using mul_dividedPower_mem_extensionSpan T x (T.mul_mem ht hu) n
  | zero => simp
  | add a b _ _ ha hb => simpa only [mul_add] using add_mem ha hb
  | neg a _ ha => simpa only [mul_neg] using neg_mem ha

/-- Right multiplication by an adjoined divided power preserves the ordered span. -/
theorem mul_dividedPower_mem_extensionSpan_of_mem {T : Subring A} {x a : A}
    (ha : a ∈ dividedPowerExtensionSpan T x) (n : ℕ) :
    a * dividedPower n x ∈ dividedPowerExtensionSpan T x := by
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
      obtain ⟨t, ht, m, rfl⟩ := ha
      rw [mul_assoc, mul_dividedPower, mul_smul_comm]
      exact AddSubgroup.nsmul_mem _ (mul_dividedPower_mem_extensionSpan T x ht (m + n)) _
  | zero => simp
  | add a b _ _ ha hb => simpa only [add_mul] using add_mem ha hb
  | neg a _ ha => simpa only [neg_mul] using neg_mem ha

/-- A collected element may be multiplied on the right by an element whose products with all
adjoined divided powers can themselves be collected. -/
theorem mul_mem_extensionSpan_of_forall {T : Subring A} {x a b : A}
    (ha : a ∈ dividedPowerExtensionSpan T x)
    (hb : ∀ n, dividedPower n x * b ∈ dividedPowerExtensionSpan T x) :
    a * b ∈ dividedPowerExtensionSpan T x := by
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
      obtain ⟨t, ht, n, rfl⟩ := ha
      simpa only [mul_assoc] using mul_mem_extensionSpan_of_mem ht (hb n)
  | zero => simp
  | add a c _ _ ha hc => simpa only [add_mul] using add_mem ha hc
  | neg a _ ha => simpa only [neg_mul] using neg_mem ha

/-- Collecting the divided powers past generators suffices to collect them past the entire
coefficient ring. -/
theorem dividedPower_mul_mem_extensionSpan_of_generators {s : Set A} {x : A}
    (h : ∀ g ∈ s, ∀ n, dividedPower n x * g ∈ dividedPowerExtensionSpan (Subring.closure s) x)
    {t : A} (ht : t ∈ Subring.closure s) (n : ℕ) :
    dividedPower n x * t ∈ dividedPowerExtensionSpan (Subring.closure s) x := by
  induction ht using Subring.closure_induction generalizing n with
  | mem g hg => exact h g hg n
  | zero => simp
  | one => simp
  | add a b _ _ ha hb => simpa only [mul_add] using add_mem (ha n) (hb n)
  | neg a _ ha => simpa only [mul_neg] using neg_mem (ha n)
  | mul a b _ _ ha hb =>
      simpa only [mul_assoc] using mul_mem_extensionSpan_of_forall (ha n) hb

/-- If the adjoined divided powers collect past the coefficient-ring generators, the ring they
generate together has precisely the ordered integral span. -/
theorem toAddSubgroup_closure_union_range_dividedPower {s : Set A} {x : A}
    (h : ∀ g ∈ s, ∀ n, dividedPower n x * g ∈ dividedPowerExtensionSpan (Subring.closure s) x) :
    (Subring.closure (s ∪ Set.range (fun n => dividedPower n x))).toAddSubgroup =
      dividedPowerExtensionSpan (Subring.closure s) x := by
  let T := Subring.closure s
  let S := dividedPowerExtensionSpan T x
  have hmul {a b : A} (ha : a ∈ S) (hb : b ∈ S) : a * b ∈ S := by
    induction hb using AddSubgroup.closure_induction with
    | mem b hb =>
        obtain ⟨t, ht, n, rfl⟩ := hb
        have hcollect := mul_mem_extensionSpan_of_forall ha
          (fun m => dividedPower_mul_mem_extensionSpan_of_generators h ht m)
        simpa only [← mul_assoc] using mul_dividedPower_mem_extensionSpan_of_mem hcollect n
    | zero => simp
    | add b c _ _ hb hc => simpa only [mul_add] using add_mem hb hc
    | neg b _ hb => simpa only [mul_neg] using neg_mem hb
  let U : Subring A := { S with
    one_mem' := mem_extensionSpan_of_mem T.one_mem
    mul_mem' := hmul }
  apply le_antisymm
  · have hle : Subring.closure (s ∪ Set.range (fun n => dividedPower n x)) ≤ U := by
      rw [Subring.closure_le]
      rintro g (hg | ⟨n, rfl⟩)
      · exact mem_extensionSpan_of_mem (Subring.subset_closure hg)
      · exact dividedPower_mem_extensionSpan T x n
    exact hle
  · rw [dividedPowerExtensionSpan_le_iff]
    intro t ht n
    exact (Subring.closure (s ∪ Set.range (fun n => dividedPower n x))).mul_mem
      ((Subring.closure_mono Set.subset_union_left) ht)
      (Subring.subset_closure (Set.mem_union_right _ ⟨n, rfl⟩))

/-- The ordered extension span as a product of integral submodules. This permits iteration of
the collection criterion without choosing expansions of the coefficients. -/
theorem dividedPowerExtensionSpan_eq_mul (T : Subring A) (x : A) :
    dividedPowerExtensionSpan T x =
      (T.toAddSubgroup.toIntSubmodule *
        dividedPowerLattice x).toAddSubgroup := by
  rw [dividedPowerLattice_def, ← Submodule.span_int_eq (T.toAddSubgroup),
    Submodule.toAddSubgroup_toIntSubmodule, Submodule.span_mul_span,
    Submodule.span_int_eq_addSubgroupClosure]
  unfold dividedPowerExtensionSpan
  apply congrArg AddSubgroup.closure
  ext a
  constructor
  · rintro ⟨t, ht, n, rfl⟩
    exact ⟨t, ht, _, ⟨n, rfl⟩, rfl⟩
  · rintro ⟨t, ht, _, ⟨n, rfl⟩, rfl⟩
    exact ⟨t, ht, n, rfl⟩

/-- The integral span of the divided powers of one element is already a subring. -/
theorem toAddSubgroup_closure_range_dividedPower (x : A) :
    (Subring.closure (Set.range (fun n => dividedPower n x))).toAddSubgroup =
      (dividedPowerLattice x).toAddSubgroup := by
  rw [dividedPowerLattice_def, Submodule.span_int_eq_addSubgroupClosure]
  apply toAddSubgroup_closure_of_one_mem_of_mul_mem
  · simpa using (AddSubgroup.subset_closure ⟨0, rfl⟩ :
      dividedPower 0 x ∈ AddSubgroup.closure (Set.range (fun n => dividedPower n x)))
  · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    rw [mul_dividedPower]
    exact (AddSubgroup.closure (Set.range (fun n => dividedPower n x))).nsmul_mem
      (AddSubgroup.subset_closure ⟨m + n, rfl⟩) _

/-- Commuting divided powers collect without introducing correction terms. -/
theorem dividedPower_mul_mem_extensionSpan_of_commute (T : Subring A) {x g : A}
    (h : Commute x g) (hg : ∀ k, dividedPower k g ∈ T) (m n : ℕ) :
    dividedPower m x * dividedPower n g ∈ dividedPowerExtensionSpan T x := by
  rw [(commute_dividedPower_dividedPower h m n).eq]
  exact mul_dividedPower_mem_extensionSpan T x (hg n) m

/-- A central integral commutator gives an integral collection rule over any coefficient ring
containing the divided powers of the crossed generator and the correction term. -/
theorem dividedPower_mul_mem_extensionSpan_of_central_commutator (T : Subring A)
    {x g z : A} (c : ℤ) (h : x * g = g * x + c • z) (hxz : Commute x z)
    (hgz : Commute g z) (hg : ∀ k, dividedPower k g ∈ T)
    (hz : ∀ k, dividedPower k z ∈ T) (m n : ℕ) :
    dividedPower m x * dividedPower n g ∈ dividedPowerExtensionSpan T x := by
  rw [dividedPower_mul_dividedPower_of_commutator_eq h (hxz.smul_right c)
    (hgz.smul_right c)]
  apply sum_mem
  intro k _
  apply mul_dividedPower_mem_extensionSpan
  exact T.mul_mem (hg _) (by rw [dividedPower_zsmul]; exact T.zsmul_mem (hz _) _)

/-- Adjoining the divided powers of `x` to the ring generated by a set `s` of divided powers, each
of whose generators commutes with `x`, gives the ordered extension span. -/
theorem toAddSubgroup_closure_union_range_dividedPower_of_commute {s : Set A} {x : A}
    (h : ∀ g ∈ s, ∃ y, Commute x y ∧ g ∈ Set.range (fun n => dividedPower n y) ∧
      ∀ k, dividedPower k y ∈ s) :
    (Subring.closure (s ∪ Set.range (fun n => dividedPower n x))).toAddSubgroup =
      dividedPowerExtensionSpan (Subring.closure s) x := by
  apply toAddSubgroup_closure_union_range_dividedPower
  intro g hg m
  obtain ⟨y, hxy, ⟨k, rfl⟩, hs⟩ := h g hg
  exact dividedPower_mul_mem_extensionSpan_of_commute _ hxy
    (fun k => Subring.subset_closure (hs k)) m k

end Subring
