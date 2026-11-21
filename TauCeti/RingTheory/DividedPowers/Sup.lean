/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.DPMorphism
import TauCeti.RingTheory.DividedPowers.Generators

/-!
# Gluing divided powers on compatible sums of ideals

Given ideals `I` and `J` of a commutative ring `A` carrying divided power structures `hI` and `hJ`
that agree in every degree on the intersection `I ⊓ J`, this file constructs the unique divided
power structure `DividedPowers.sup hI hJ hagree` on the sum `I ⊔ J` restricting to `hI` on `I` and
to `hJ` on `J` (Stacks Project, Lemma 23.2.5, tag 07GQ).

The operation on a sum `x + y` (`x ∈ I`, `y ∈ J`) is given by the convolution
`DividedPowers.convolution hI hJ n x y = ∑ k ∈ antidiagonal n, hI.dpow k.1 x * hJ.dpow k.2 y`,
which is the `n`-th coefficient of the power-series product `hI.exp x * hJ.exp y`. Agreement of
`hI` and `hJ` on `I ⊓ J` ensures independence of the decomposition via `DividedPowers.exp_add`,
yielding an `AdditivePowers (I ⊔ J)` candidate whose multiplication and iteration identities on the
generating set `(I : Set A) ∪ (J : Set A)` follow from `hI` and `hJ` and upgrade to
`DividedPowers (I ⊔ J)` by `DividedPowers.AdditivePowers.toDividedPowers`.

When `I ⊓ J = I * J` (as occurs for `IΓ` and `Γ_R(M)₊` in a divided power algebra), Mathlib's
`DividedPowers.coincide_on_smul` supplies agreement on `I ⊓ J` automatically, giving
`DividedPowers.supOfInfEqMul`.

## Main declarations

* `DividedPowers.convolution`: antidiagonal convolution of two divided power structures.
* `DividedPowers.convolution_eq_of_add_eq`: independence of `convolution` from the decomposition
  `x + y = x' + y'` when `hI` and `hJ` agree on `I ⊓ J`.
* `DividedPowers.sup`: the unique glued `DividedPowers (I ⊔ J)` when `hI` and `hJ` agree on
  `I ⊓ J`.
* `DividedPowers.isDPMorphism_sup_iff`: universal property of `DividedPowers.sup` for outgoing
  divided power morphisms.
* `DividedPowers.eq_sup_iff` and `DividedPowers.exists_sup_iff`: characterization of existence and
  uniqueness of a common extension to `I ⊔ J`.
* `DividedPowers.supOfInfEqMul`: gluing when `I ⊓ J = I * J`.

## References

* [Stacks Project, Divided Power Algebra, Lemma 23.2.5 (Tag 07GQ)](https://stacks.math.columbia.edu/tag/07GQ)
-/

public section

open Finset

namespace DividedPowers

section CommSemiring

variable {A : Type*} [CommSemiring A] {I J : Ideal A}

/-- The antidiagonal convolution `∑_{i + j = n} hI.dpow i x * hJ.dpow j y` of two divided power
structures `hI` on `I` and `hJ` on `J`. -/
def convolution (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (x y : A) : A :=
  ∑ k ∈ antidiagonal n, hI.dpow k.1 x * hJ.dpow k.2 y

/-- The defining equation of `DividedPowers.convolution`. -/
theorem convolution_def (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (x y : A) :
    convolution hI hJ n x y = ∑ k ∈ antidiagonal n, hI.dpow k.1 x * hJ.dpow k.2 y :=
  (rfl)

/-- `convolution hI hJ n x y` is the `n`-th coefficient of the product of divided-power
exponentials `hI.exp x * hJ.exp y`. -/
theorem convolution_eq_coeff_exp_mul (hI : DividedPowers I) (hJ : DividedPowers J)
    (n : ℕ) (x y : A) :
    convolution hI hJ n x y = PowerSeries.coeff n (hI.exp x * hJ.exp y) := by
  rw [convolution_def, PowerSeries.coeff_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  simp only [DividedPowers.exp, PowerSeries.coeff_mk]

/-- Convolution is symmetric in the two divided-power structures and arguments. -/
theorem convolution_comm (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (x y : A) :
    convolution hI hJ n x y = convolution hJ hI n y x := by
  rw [convolution_eq_coeff_exp_mul, convolution_eq_coeff_exp_mul, mul_comm]

/-- In degree `0`, the convolution of elements of `I` and `J` equals `1`. -/
@[simp]
theorem convolution_zero (hI : DividedPowers I) (hJ : DividedPowers J)
    {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    convolution hI hJ 0 x y = 1 := by
  simp [convolution_def, hI.dpow_zero hx, hJ.dpow_zero hy]

/-- In degree `1`, the convolution of elements of `I` and `J` equals `x + y`. -/
@[simp]
theorem convolution_one (hI : DividedPowers I) (hJ : DividedPowers J)
    {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    convolution hI hJ 1 x y = x + y := by
  rw [convolution_def, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [sum_range_succ, hI.dpow_zero hx, hI.dpow_one hx, hJ.dpow_zero hy, hJ.dpow_one hy, add_comm]

/-- Convolution with `0` on the right recovers `hI.dpow` on all of `A`. -/
@[simp]
theorem convolution_zero_right (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (x : A) :
    convolution hI hJ n x 0 = hI.dpow n x := by
  rw [convolution_def, sum_eq_single (n, 0)]
  · rw [hJ.dpow_zero J.zero_mem, mul_one]
  · intro k hk hne
    have hk2 : k.2 ≠ 0 := by
      intro h0
      apply hne
      have hsum := mem_antidiagonal.mp hk
      exact Prod.ext (by omega) h0
    rw [hJ.dpow_eval_zero hk2, mul_zero]
  · intro hn
    exact absurd (mem_antidiagonal.mpr (add_zero n)) hn

/-- Convolution with `0` on the left recovers `hJ.dpow` on all of `A`. -/
@[simp]
theorem convolution_zero_left (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ) (y : A) :
    convolution hI hJ n 0 y = hJ.dpow n y := by
  rw [convolution_comm, convolution_zero_right]

/-- In positive degree, the convolution of `x ∈ I` and `y ∈ J` lies in `I ⊔ J`. -/
theorem convolution_mem (hI : DividedPowers I) (hJ : DividedPowers J)
    {n : ℕ} (hn : n ≠ 0) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    convolution hI hJ n x y ∈ I ⊔ J := by
  rw [convolution_def]
  refine Submodule.sum_mem _ fun k hk ↦ ?_
  have hsum := mem_antidiagonal.mp hk
  by_cases h1 : k.1 = 0
  · have h2 : k.2 ≠ 0 := by omega
    exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (hJ.dpow_mem h2 hy))
  · exact Ideal.mul_mem_right _ _ (Ideal.mem_sup_left (hI.dpow_mem h1 hx))

/-- Convolution is homogeneous of degree `n` under simultaneous scalar multiplication. -/
theorem convolution_mul (hI : DividedPowers I) (hJ : DividedPowers J)
    (n : ℕ) (a : A) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    convolution hI hJ n (a * x) (a * y) = a ^ n * convolution hI hJ n x y := by
  rw [convolution_def, convolution_def, mul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [hI.dpow_mul hx, hJ.dpow_mul hy, mul_mul_mul_comm, ← pow_add, mem_antidiagonal.mp hk]

/-- Convolution satisfies the divided-power addition law on pairs `(x + x', y + y')`. -/
theorem convolution_add (hI : DividedPowers I) (hJ : DividedPowers J) (n : ℕ)
    {x x' y y' : A} (hx : x ∈ I) (hx' : x' ∈ I) (hy : y ∈ J) (hy' : y' ∈ J) :
    convolution hI hJ n (x + x') (y + y') =
      ∑ k ∈ antidiagonal n, convolution hI hJ k.1 x y * convolution hI hJ k.2 x' y' := by
  have hexp : hI.exp (x + x') * hJ.exp (y + y') =
      (hI.exp x * hJ.exp y) * (hI.exp x' * hJ.exp y') := by
    rw [hI.exp_add hx hx', hJ.exp_add hy hy']
    ring
  rw [convolution_eq_coeff_exp_mul, hexp, PowerSeries.coeff_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [convolution_eq_coeff_exp_mul, convolution_eq_coeff_exp_mul]

/-- The convolution of `hI` with itself computes `hI.dpow n (x + y)` for `x, y ∈ I`. -/
theorem convolution_self (hI : DividedPowers I) (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    convolution hI hI n x y = hI.dpow n (x + y) :=
  (hI.dpow_add hx hy).symm

end CommSemiring

section CommRing

variable {A : Type*} [CommRing A] {I J : Ideal A}

/-- **Well-definedness of convolution** (Stacks 23.2.5, tag 07GQ): if `hI` and `hJ` agree in every
degree on `I ⊓ J`, then `convolution hI hJ n x y` depends only on the sum `x + y`. -/
theorem convolution_eq_of_add_eq (hI : DividedPowers I) (hJ : DividedPowers J)
    (hagree : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) (n : ℕ)
    {x x' y y' : A} (hx : x ∈ I) (hx' : x' ∈ I) (hy : y ∈ J) (hy' : y' ∈ J)
    (hxy : x + y = x' + y') :
    convolution hI hJ n x y = convolution hI hJ n x' y' := by
  have hwI : x - x' ∈ I := I.sub_mem hx hx'
  have hweq : x - x' = y' - y := sub_eq_sub_iff_add_eq_add.mpr (by rw [hxy, add_comm])
  have hwJ : x - x' ∈ J := hweq ▸ J.sub_mem hy' hy
  have hexpw : hI.exp (x - x') = hJ.exp (x - x') := by
    ext k
    simp only [DividedPowers.exp, PowerSeries.coeff_mk]
    exact hagree k (x - x') ⟨hwI, hwJ⟩
  have hexp : hI.exp x * hJ.exp y = hI.exp x' * hJ.exp y' := by
    have hx_eq : x = x' + (x - x') := by ring
    have hy'_eq : y' = (x - x') + y := by rw [hweq]; ring
    rw [hx_eq, hI.exp_add hx' hwI, mul_assoc, hexpw, ← hJ.exp_add hwJ hy, ← hy'_eq]
  rw [convolution_eq_coeff_exp_mul, convolution_eq_coeff_exp_mul, hexp]

private noncomputable def supDpow (hI : DividedPowers I) (hJ : DividedPowers J)
    (n : ℕ) (z : A) : A :=
  open scoped Classical in
  if hz : z ∈ I ⊔ J then
    let h := Submodule.mem_sup.mp hz
    convolution hI hJ n h.choose h.choose_spec.2.choose
  else 0

private theorem supDpow_add_eq (hI : DividedPowers I) (hJ : DividedPowers J)
    (hagree : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    supDpow hI hJ n (x + y) = convolution hI hJ n x y := by
  classical
  have hxy : x + y ∈ I ⊔ J := Submodule.add_mem_sup hx hy
  simp only [supDpow, dite_eq_left hxy]
  set h := Submodule.mem_sup.mp hxy
  exact convolution_eq_of_add_eq hI hJ hagree n h.choose_spec.1 hx
    h.choose_spec.2.choose_spec.1 hy h.choose_spec.2.choose_spec.2

private noncomputable def supAdditivePowers (hI : DividedPowers I) (hJ : DividedPowers J)
    (hagree : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) :
    AdditivePowers (I ⊔ J) where
  dpow := supDpow hI hJ
  dpow_null {n z} hz := by
    classical
    simp [supDpow, hz]
  dpow_zero {z} hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [supDpow_add_eq hI hJ hagree 0 hx hy, convolution_zero hI hJ hx hy]
  dpow_one {z} hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [supDpow_add_eq hI hJ hagree 1 hx hy, convolution_one hI hJ hx hy]
  dpow_mem {n z} hn hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [supDpow_add_eq hI hJ hagree n hx hy]
    exact convolution_mem hI hJ hn hx hy
  dpow_add {n z z'} hz hz' := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨x', hx', y', hy', rfl⟩ := Submodule.mem_sup.mp hz'
    have hsum : x + y + (x' + y') = (x + x') + (y + y') := by ring
    rw [hsum, supDpow_add_eq hI hJ hagree n (I.add_mem hx hx') (J.add_mem hy hy'),
      convolution_add hI hJ n hx hx' hy hy']
    refine sum_congr rfl fun k _ ↦ ?_
    rw [supDpow_add_eq hI hJ hagree k.1 hx hy, supDpow_add_eq hI hJ hagree k.2 hx' hy']
  dpow_mul {n a z} hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [mul_add, supDpow_add_eq hI hJ hagree n (I.mul_mem_left a hx) (J.mul_mem_left a hy),
      convolution_mul hI hJ n a hx hy, supDpow_add_eq hI hJ hagree n hx hy]

private theorem supAdditivePowers_dpow_of_mem_left (hI : DividedPowers I) (hJ : DividedPowers J)
    (hagree : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) (n : ℕ) {x : A} (hx : x ∈ I) :
    (supAdditivePowers hI hJ hagree).dpow n x = hI.dpow n x := by
  dsimp only [supAdditivePowers]
  simpa only [add_zero] using
    (supDpow_add_eq hI hJ hagree n hx J.zero_mem).trans (convolution_zero_right hI hJ n x)

private theorem supAdditivePowers_dpow_of_mem_right (hI : DividedPowers I) (hJ : DividedPowers J)
    (hagree : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) (n : ℕ) {y : A} (hy : y ∈ J) :
    (supAdditivePowers hI hJ hagree).dpow n y = hJ.dpow n y := by
  dsimp only [supAdditivePowers]
  simpa only [zero_add] using
    (supDpow_add_eq hI hJ hagree n I.zero_mem hy).trans (convolution_zero_left hI hJ n y)

/-- **Gluing divided powers on a compatible sum of ideals** (Stacks 23.2.5, tag 07GQ): given
divided power structures `hI` on `I` and `hJ` on `J` that agree on `I ⊓ J`, there is a unique
divided power structure on `I ⊔ J` restricting to `hI` on `I` and to `hJ` on `J`. -/
noncomputable def sup (hI : DividedPowers I) (hJ : DividedPowers J)
    (hagree : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) :
    DividedPowers (I ⊔ J) :=
  (supAdditivePowers hI hJ hagree).toDividedPowers
    (S := (I : Set A) ∪ (J : Set A))
    (by rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq])
    (fun s hs m n ↦ by
      rcases hs with hs | hs
      · simp only [supAdditivePowers_dpow_of_mem_left hI hJ hagree _ hs]
        exact hI.mul_dpow hs
      · simp only [supAdditivePowers_dpow_of_mem_right hI hJ hagree _ hs]
        exact hJ.mul_dpow hs)
    (fun s hs m {n} hn ↦ by
      rcases hs with hs | hs
      · simp only [supAdditivePowers_dpow_of_mem_left hI hJ hagree _ hs,
          supAdditivePowers_dpow_of_mem_left hI hJ hagree _ (hI.dpow_mem hn hs)]
        exact hI.dpow_comp hn hs
      · simp only [supAdditivePowers_dpow_of_mem_right hI hJ hagree _ hs,
          supAdditivePowers_dpow_of_mem_right hI hJ hagree _ (hJ.dpow_mem hn hs)]
        exact hJ.dpow_comp hn hs)

/-- On a sum `x + y` with `x ∈ I` and `y ∈ J`, the glued divided powers equal the convolution
`convolution hI hJ n x y`. -/
theorem sup_dpow_add (hI : DividedPowers I) (hJ : DividedPowers J)
    (hagree : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    (hI.sup hJ hagree).dpow n (x + y) = convolution hI hJ n x y := by
  rw [sup, AdditivePowers.toDividedPowers_dpow]
  exact supDpow_add_eq hI hJ hagree n hx hy

/-- On `I`, the glued divided powers agree with `hI`. -/
@[simp]
theorem sup_dpow_of_mem_left (hI : DividedPowers I) (hJ : DividedPowers J)
    (hagree : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {x : A} (hx : x ∈ I) :
    (hI.sup hJ hagree).dpow n x = hI.dpow n x := by
  rw [sup, AdditivePowers.toDividedPowers_dpow]
  exact supAdditivePowers_dpow_of_mem_left hI hJ hagree n hx

/-- On `J`, the glued divided powers agree with `hJ`. -/
@[simp]
theorem sup_dpow_of_mem_right (hI : DividedPowers I) (hJ : DividedPowers J)
    (hagree : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (n : ℕ) {y : A} (hy : y ∈ J) :
    (hI.sup hJ hagree).dpow n y = hJ.dpow n y := by
  rw [sup, AdditivePowers.toDividedPowers_dpow]
  exact supAdditivePowers_dpow_of_mem_right hI hJ hagree n hy

/-- The identity ring homomorphism is a divided power morphism from `(I, hI)` to
`(I ⊔ J, hI.sup hJ hagree)`. -/
theorem isDPMorphism_id_sup_left (hI : DividedPowers I) (hJ : DividedPowers J)
    (hagree : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) :
    IsDPMorphism hI (hI.sup hJ hagree) (RingHom.id A) where
  ideal_comp := by rw [Ideal.map_id]; exact le_sup_left
  dpow_comp {n} a ha := by
    simpa only [RingHom.id_apply] using sup_dpow_of_mem_left hI hJ hagree n ha

/-- The identity ring homomorphism is a divided power morphism from `(J, hJ)` to
`(I ⊔ J, hI.sup hJ hagree)`. -/
theorem isDPMorphism_id_sup_right (hI : DividedPowers I) (hJ : DividedPowers J)
    (hagree : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) :
    IsDPMorphism hJ (hI.sup hJ hagree) (RingHom.id A) where
  ideal_comp := by rw [Ideal.map_id]; exact le_sup_right
  dpow_comp {n} a ha := by
    simpa only [RingHom.id_apply] using sup_dpow_of_mem_right hI hJ hagree n ha

/-- Universal property of `DividedPowers.sup`: a ring homomorphism `g : A →+* C` is a divided power
morphism out of `(I ⊔ J, hI.sup hJ hagree)` if and only if it is a divided power morphism out of
both `(I, hI)` and `(J, hJ)`. -/
theorem isDPMorphism_sup_iff {C : Type*} [CommSemiring C] {K : Ideal C}
    (hI : DividedPowers I) (hJ : DividedPowers J)
    (hagree : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (hK : DividedPowers K) (g : A →+* C) :
    IsDPMorphism (hI.sup hJ hagree) hK g ↔ IsDPMorphism hI hK g ∧ IsDPMorphism hJ hK g := by
  refine ⟨fun hg ↦ ⟨?_, ?_⟩, fun ⟨hgI, hgJ⟩ ↦ ?_⟩
  · simpa only [RingHom.comp_id] using hg.comp hK (isDPMorphism_id_sup_left hI hJ hagree)
  · simpa only [RingHom.comp_id] using hg.comp hK (isDPMorphism_id_sup_right hI hJ hagree)
  · refine IsDPMorphism.on_span (hI.sup hJ hagree) hK (S := (I : Set A) ∪ (J : Set A))
      (by rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq]) (fun s hs ↦ ?_) (fun {n} s hs ↦ ?_)
    · rcases hs with hs | hs
      · exact hgI.ideal_comp (Ideal.mem_map_of_mem g hs)
      · exact hgJ.ideal_comp (Ideal.mem_map_of_mem g hs)
    · rcases hs with hs | hs
      · rw [sup_dpow_of_mem_left hI hJ hagree n hs, hgI.dpow_comp s hs]
      · rw [sup_dpow_of_mem_right hI hJ hagree n hs, hgJ.dpow_comp s hs]

/-- Uniqueness of `DividedPowers.sup`: a divided power structure on `I ⊔ J` equals
`hI.sup hJ hagree` if and only if it restricts to `hI` on `I` and to `hJ` on `J`. -/
theorem eq_sup_iff (hI : DividedPowers I) (hJ : DividedPowers J)
    (hagree : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w)
    (hIJ : DividedPowers (I ⊔ J)) :
    hIJ = hI.sup hJ hagree ↔
      (∀ n, ∀ x ∈ I, hIJ.dpow n x = hI.dpow n x) ∧
      (∀ n, ∀ y ∈ J, hIJ.dpow n y = hJ.dpow n y) := by
  refine ⟨fun h ↦ h ▸ ⟨fun n _ hx ↦ sup_dpow_of_mem_left hI hJ hagree n hx,
    fun n _ hy ↦ sup_dpow_of_mem_right hI hJ hagree n hy⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  refine DividedPowers.dpow_eq_from_gens (hI.sup hJ hagree) hIJ
    (S := (I : Set A) ∪ (J : Set A))
    (by rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq]) fun {n} s hs ↦ ?_
  rcases hs with hs | hs
  · rw [sup_dpow_of_mem_left hI hJ hagree n hs, h1 n s hs]
  · rw [sup_dpow_of_mem_right hI hJ hagree n hs, h2 n s hs]

/-- Existence criterion for gluing divided powers (Stacks 23.2.5, tag 07GQ): a divided power
structure on `I ⊔ J` restricting to `hI` on `I` and to `hJ` on `J` exists if and only if `hI` and
`hJ` agree on `I ⊓ J` in every degree. -/
theorem exists_sup_iff (hI : DividedPowers I) (hJ : DividedPowers J) :
    (∃ hIJ : DividedPowers (I ⊔ J),
        (∀ n, ∀ x ∈ I, hIJ.dpow n x = hI.dpow n x) ∧
        (∀ n, ∀ y ∈ J, hIJ.dpow n y = hJ.dpow n y)) ↔
      ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w := by
  refine ⟨fun ⟨hIJ, h1, h2⟩ n w hw ↦ ?_, fun hagree ↦
    ⟨hI.sup hJ hagree, fun n _ hx ↦ sup_dpow_of_mem_left hI hJ hagree n hx,
      fun n _ hy ↦ sup_dpow_of_mem_right hI hJ hagree n hy⟩⟩
  rw [← h1 n w hw.1, h2 n w hw.2]

/-- **Gluing when intersection equals product** (Stacks 23.2.5, tag 07GQ): if `I ⊓ J = I * J`, then
`hI` and `hJ` automatically agree on `I ⊓ J` by `DividedPowers.coincide_on_smul`, and glue uniquely
to a divided power structure on `I ⊔ J`. -/
noncomputable def supOfInfEqMul (hI : DividedPowers I) (hJ : DividedPowers J)
    (hinf : I ⊓ J = I * J) : DividedPowers (I ⊔ J) :=
  hI.sup hJ fun _ _ hw ↦ hI.coincide_on_smul hJ (by simpa only [hinf, smul_eq_mul] using hw)

/-- `supOfInfEqMul` agrees with `sup` for any compatibility proof on `I ⊓ J`. -/
theorem supOfInfEqMul_eq_sup (hI : DividedPowers I) (hJ : DividedPowers J)
    (hinf : I ⊓ J = I * J) (hagree : ∀ n, ∀ w ∈ I ⊓ J, hI.dpow n w = hJ.dpow n w) :
    hI.supOfInfEqMul hJ hinf = hI.sup hJ hagree := (rfl)

/-- On `x + y` with `x ∈ I` and `y ∈ J`, `supOfInfEqMul` equals `convolution hI hJ n x y`. -/
theorem supOfInfEqMul_dpow_add (hI : DividedPowers I) (hJ : DividedPowers J)
    (hinf : I ⊓ J = I * J) (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    (hI.supOfInfEqMul hJ hinf).dpow n (x + y) = convolution hI hJ n x y := by
  rw [supOfInfEqMul]
  exact sup_dpow_add hI hJ _ n hx hy

/-- On `I`, `supOfInfEqMul` agrees with `hI`. -/
@[simp]
theorem supOfInfEqMul_dpow_of_mem_left (hI : DividedPowers I) (hJ : DividedPowers J)
    (hinf : I ⊓ J = I * J) (n : ℕ) {x : A} (hx : x ∈ I) :
    (hI.supOfInfEqMul hJ hinf).dpow n x = hI.dpow n x := by
  rw [supOfInfEqMul]
  exact sup_dpow_of_mem_left hI hJ _ n hx

/-- On `J`, `supOfInfEqMul` agrees with `hJ`. -/
@[simp]
theorem supOfInfEqMul_dpow_of_mem_right (hI : DividedPowers I) (hJ : DividedPowers J)
    (hinf : I ⊓ J = I * J) (n : ℕ) {y : A} (hy : y ∈ J) :
    (hI.supOfInfEqMul hJ hinf).dpow n y = hJ.dpow n y := by
  rw [supOfInfEqMul]
  exact sup_dpow_of_mem_right hI hJ _ n hy

/-- Universal property of `DividedPowers.supOfInfEqMul` for outgoing divided power morphisms. -/
theorem isDPMorphism_supOfInfEqMul_iff {C : Type*} [CommSemiring C] {K : Ideal C}
    (hI : DividedPowers I) (hJ : DividedPowers J) (hinf : I ⊓ J = I * J)
    (hK : DividedPowers K) (g : A →+* C) :
    IsDPMorphism (hI.supOfInfEqMul hJ hinf) hK g ↔
      IsDPMorphism hI hK g ∧ IsDPMorphism hJ hK g := by
  rw [supOfInfEqMul]
  exact isDPMorphism_sup_iff hI hJ _ hK g

/-- Uniqueness of `DividedPowers.supOfInfEqMul`: a divided power structure on `I ⊔ J` equals
`hI.supOfInfEqMul hJ hinf` if and only if it restricts to `hI` on `I` and to `hJ` on `J`. -/
theorem eq_supOfInfEqMul_iff (hI : DividedPowers I) (hJ : DividedPowers J)
    (hinf : I ⊓ J = I * J) (hIJ : DividedPowers (I ⊔ J)) :
    hIJ = hI.supOfInfEqMul hJ hinf ↔
      (∀ n, ∀ x ∈ I, hIJ.dpow n x = hI.dpow n x) ∧
      (∀ n, ∀ y ∈ J, hIJ.dpow n y = hJ.dpow n y) := by
  rw [supOfInfEqMul]
  exact eq_sup_iff hI hJ _ hIJ

end CommRing

end DividedPowers
