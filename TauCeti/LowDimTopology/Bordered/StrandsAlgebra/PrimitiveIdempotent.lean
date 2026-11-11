/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Sort
public import Mathlib.RingTheory.Idempotents
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# The primitive idempotents of the matched subalgebra

The algebra `A(Z)` of a pointed matched circle, the matched subalgebra of the strands algebra
(`TauCeti.StrandsAlgebra.matchedSubalgebra`), has the idempotents `I(s)`
(`TauCeti.StrandsAlgebra.matchedIdem`), one for each set `s` of matched pairs. They are orthogonal
and sum to the unit, and this file shows that they are **primitive** idempotents of `A(Z)`, provided
the ground ring has no idempotents besides `0` and `1`; over `𝔽₂` they are therefore the primitive
idempotents of a complete orthogonal decomposition of the unit, which is the ring of idempotents
over which type `D` structures and type `A` modules of bordered Floer theory are defined. Precisely,
`I(s)` is primitive exactly when `s` consists of matched pairs and `1` is primitive in the ground
ring (`TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem_iff`).

The proof uses a filtration of the strands algebra by the total length of the strands. The
*length* of a strand diagram (`TauCeti.StrandDiagram.length`) is the number of points of `α`
passed by its strands, counted with multiplicity: with `pos x` the position of `x` in `α`, it is
`∑ (pos (φ x) - pos x)` over the starting points `x`. It adds under concatenation and vanishes
exactly on the identity diagrams `I(S)`. The elements supported on the diagrams of length at least
`k` form a filtration (`TauCeti.StrandsAlgebra.lengthFiltration`) with `F_a F_b ⊆ F_{a+b}`; since
lengths are bounded, every element of `F_1`, which consists of the elements with no identity
diagram in their support, is nilpotent.

An element `f` of the corner ring `I(s) A(Z) I(s)` takes the same value `c` at every identity
diagram `I(S)` with `S` a set of points over `s`, because the coefficients of an element of the
matched subalgebra do not change when a horizontal strand moves within a matched pair, and it
vanishes at the other identity diagrams. So `f - c I(s)` lies in `F_1`. When `f` is idempotent,
reducing `f² = f` modulo `F_1` shows that `c` is an idempotent of the ground ring, so `c = 0` or
`c = 1`, and then `f` or `I(s) - f` is an idempotent in `F_1`, hence nilpotent and zero.

## Main definitions

* `TauCeti.StrandDiagram.length`: the total length of the strands of a diagram.
* `TauCeti.StrandsAlgebra.lengthFiltration R k`: the elements supported on the diagrams of length
  at least `k`.

## Main results

* `TauCeti.StrandDiagram.length_trans`: lengths add under concatenation.
* `TauCeti.StrandDiagram.length_eq_zero_iff`: the diagrams of length zero are the identity
  diagrams.
* `TauCeti.StrandsAlgebra.mul_mem_lengthFiltration`: `F_a F_b ⊆ F_{a+b}`.
* `TauCeti.StrandsAlgebra.isNilpotent_of_mem_lengthFiltration_one`: the elements of `F_1` are
  nilpotent.
* `TauCeti.StrandsAlgebra.eq_zero_or_eq_matchedIdem_of_isIdempotentElem`: when `1` is primitive in
  the ground ring, the only idempotents of the corner ring of `I(s)` in the matched subalgebra are
  `0` and `I(s)`.
* `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem_iff`: `I(s)` is a primitive idempotent
  of the matched subalgebra exactly when `s` is a set of matched pairs and `1` is primitive in the
  ground ring.
* `TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_matchedIdem`: the `I(s)` form a complete
  family of orthogonal idempotents of the matched subalgebra.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2 (the
  idempotents `I(s)` and the subalgebra of idempotents of `A(Z)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandDiagram

variable {α : Type*} [LinearOrder α] [Fintype α]

/-- The position of a point of `α` in the order, counted from `0`. -/
private def pos (x : α) : ℕ :=
  (monoEquivOfFin α rfl).symm x

private theorem pos_le_pos_iff {x y : α} : pos x ≤ pos y ↔ x ≤ y := by
  simp only [pos, Fin.val_fin_le, OrderIso.le_iff_le]

/-- The sum of the positions of the starting points of a diagram is at most that of its end
points: each strand goes upwards. -/
private theorem sum_pos_source_le_sum_pos_target (φ : StrandDiagram α) :
    ∑ x ∈ φ.source, pos x ≤ ∑ y ∈ φ.target, pos y := by
  rw [target_eq_image, sum_image φ.injOn_getD]
  exact sum_le_sum fun x hx ↦ pos_le_pos_iff.2 (le_getD hx)

/-- The **length** of a strand diagram: the number of points of `α` passed by its strands,
counted with multiplicity, that is, the sum over the strands of the difference of the positions of
their two ends. -/
def length (φ : StrandDiagram α) : ℕ :=
  ∑ y ∈ φ.target, pos y - ∑ x ∈ φ.source, pos x

/-- **Lengths add under concatenation**: the length of the composite of a diagram `φ` with a
diagram `ψ` starting where `φ` ends is the sum of their lengths. -/
theorem length_trans {φ ψ : StrandDiagram α} (h : φ.target = ψ.source) :
    (φ.trans ψ).length = φ.length + ψ.length := by
  have hφ := φ.sum_pos_source_le_sum_pos_target
  have hψ := ψ.sum_pos_source_le_sum_pos_target
  rw [h] at hφ
  simp only [length, source_trans_of_target_eq h, target_trans_of_target_eq h, h]
  omega

/-- The identity diagrams have length zero. -/
@[simp]
theorem length_idOn (s : Finset α) : (idOn s).length = 0 := by
  simp [length]

/-- **The diagrams of length zero are the identity diagrams**, those all of whose strands are
horizontal. -/
theorem length_eq_zero_iff {φ : StrandDiagram α} : φ.length = 0 ↔ φ = idOn φ.source := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ length_idOn _⟩
  have hle : ∑ y ∈ φ.target, pos y ≤ ∑ x ∈ φ.source, pos x := Nat.sub_eq_zero_iff_le.1 h
  rw [target_eq_image, sum_image φ.injOn_getD] at hle
  -- Each strand goes upwards, so equality of the sums forces every strand to be horizontal.
  have heq := (sum_eq_sum_iff_of_le fun x hx ↦ pos_le_pos_iff.2 (le_getD hx)).1
    (le_antisymm (sum_le_sum fun x hx ↦ pos_le_pos_iff.2 (le_getD hx)) hle)
  ext i j
  by_cases hi : i ∈ φ.source
  · have hj : (φ i).getD i = i :=
      le_antisymm (pos_le_pos_iff.1 (heq i hi).ge) (le_getD hi)
    have hφi := getD_mem hi
    rw [hj, Option.mem_def] at hφi
    simp [hφi, hi]
  · simp [apply_eq_none_of_notMem_source hi, hi]

/-- A diagram which is not an identity diagram has positive length. -/
theorem one_le_length_iff {φ : StrandDiagram α} : 1 ≤ φ.length ↔ φ ≠ idOn φ.source := by
  rw [Nat.one_le_iff_ne_zero, Ne, length_eq_zero_iff]

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram

/-! ### The length filtration -/

section LengthFiltration

variable (R : Type*) {α : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

/-- The part `F_k` of the length filtration of the strands algebra: the elements supported on the
strand diagrams of length at least `k`, that is, the image of `Finsupp.supported` under the basis
of strand diagrams. -/
def lengthFiltration (k : ℕ) : Submodule R (StrandsAlgebra R α) :=
  (Finsupp.supported R R {φ : StrandDiagram α | k ≤ φ.length}).map
    ((basis R α).repr.symm : (StrandDiagram α →₀ R) →ₗ[R] StrandsAlgebra R α)

variable {R}

/-- An element lies in `F_k` exactly when every strand diagram in its support has length at least
`k`. -/
theorem mem_lengthFiltration {k : ℕ} {x : StrandsAlgebra R α} :
    x ∈ lengthFiltration R k ↔ ∀ φ ∈ ((basis R α).repr x).support, k ≤ φ.length := by
  rw [lengthFiltration, Submodule.mem_map_equiv, LinearEquiv.symm_symm, Finsupp.mem_supported]
  rfl

/-- `F_k` is the span of the strand diagrams of length at least `k`. -/
theorem lengthFiltration_eq_span (k : ℕ) :
    lengthFiltration R k = Submodule.span R (of '' {φ : StrandDiagram α | k ≤ φ.length}) := by
  rw [lengthFiltration, Finsupp.supported_eq_span_single, Submodule.map_span, ← Set.image_comp]
  congr 2
  ext φ
  simp [← basis_apply]

/-- A strand diagram of length at least `k` lies in `F_k`. -/
theorem of_mem_lengthFiltration {k : ℕ} {φ : StrandDiagram α} (h : k ≤ φ.length) :
    (of φ : StrandsAlgebra R α) ∈ lengthFiltration R k := by
  rw [lengthFiltration_eq_span]
  exact Submodule.subset_span ⟨φ, h, rfl⟩

/-- Over a nontrivial ring, a strand diagram lies in `F_k` exactly when its length is at least
`k`. -/
theorem of_mem_lengthFiltration_iff [Nontrivial R] {k : ℕ} {φ : StrandDiagram α} :
    (of φ : StrandsAlgebra R α) ∈ lengthFiltration R k ↔ k ≤ φ.length := by
  refine ⟨fun h ↦ ?_, of_mem_lengthFiltration⟩
  rw [mem_lengthFiltration, ← basis_apply, Module.Basis.repr_self,
    Finsupp.support_single _ one_ne_zero] at h
  simpa using h

/-- The filtration starts with the whole strands algebra. -/
@[simp]
theorem lengthFiltration_zero : lengthFiltration R 0 = (⊤ : Submodule R (StrandsAlgebra R α)) :=
  eq_top_iff.2 fun _ _ ↦ mem_lengthFiltration.2 fun _ _ ↦ Nat.zero_le _

/-- The length filtration is decreasing. -/
theorem lengthFiltration_antitone :
    Antitone (lengthFiltration R : ℕ → Submodule R (StrandsAlgebra R α)) :=
  fun _ _ hkl _ hx ↦ mem_lengthFiltration.2 fun φ hφ ↦ hkl.trans (mem_lengthFiltration.1 hx φ hφ)

/-- An element lies in `F_1` exactly when its coefficients at the identity diagrams vanish. -/
theorem mem_lengthFiltration_one_iff {x : StrandsAlgebra R α} :
    x ∈ lengthFiltration R 1 ↔ ∀ s : Finset α, (basis R α).repr x (idOn s) = 0 := by
  rw [mem_lengthFiltration]
  refine ⟨fun h s ↦ ?_, fun h φ hφ ↦ one_le_length_iff.2 fun hφ' ↦ ?_⟩
  · by_contra hs
    simpa using h _ (Finsupp.mem_support_iff.2 hs)
  · exact Finsupp.mem_support_iff.1 hφ (hφ' ▸ h φ.source)

/-- **The strands algebra is filtered by length**: `F_a F_b ⊆ F_{a+b}`. -/
theorem mul_mem_lengthFiltration {a b : ℕ} {x y : StrandsAlgebra R α}
    (hx : x ∈ lengthFiltration R a) (hy : y ∈ lengthFiltration R b) :
    x * y ∈ lengthFiltration R (a + b) := by
  rw [lengthFiltration_eq_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨ψ, hψ, rfl⟩ := hy
      rw [of_mul_of]
      split_ifs with hφψ
      · refine of_mem_lengthFiltration ?_
        rw [length_trans hφψ.target_eq]
        exact Nat.add_le_add hφ hψ
      · exact zero_mem _
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ hx hx' => rw [add_mul]; exact add_mem hx hx'
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

/-- The `n`-th power of an element of `F_1` lies in `F_n`. -/
theorem pow_mem_lengthFiltration {x : StrandsAlgebra R α} (hx : x ∈ lengthFiltration R 1)
    (n : ℕ) : x ^ n ∈ lengthFiltration R n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact mul_mem_lengthFiltration ih hx

/-- **The elements of `F_1` are nilpotent**: lengths of strand diagrams are bounded. -/
theorem isNilpotent_of_mem_lengthFiltration_one {x : StrandsAlgebra R α}
    (hx : x ∈ lengthFiltration R 1) : IsNilpotent x := by
  have : Nonempty (StrandDiagram α) := ⟨idOn ∅⟩
  obtain ⟨φ₀, hφ₀⟩ := Finite.exists_max (length : StrandDiagram α → ℕ)
  refine ⟨φ₀.length + 1, (basis R α).repr.injective (Finsupp.ext fun φ ↦ ?_)⟩
  by_contra hφ
  have := mem_lengthFiltration.1 (pow_mem_lengthFiltration hx (φ₀.length + 1)) φ
    (Finsupp.mem_support_iff.2 (by simpa using hφ))
  exact absurd (hφ₀ φ) (by omega)

end LengthFiltration

/-! ### The primitive idempotents of the matched subalgebra -/

section Primitive

variable {R α β : Type*} [CommSemiring R] [LinearOrder α] [Fintype α] [DecidableEq β]
  {M : α → β} {s : Finset β}

/-- Multiplying a basis element `φ` on the left by `I(s)` keeps it when its starting points lie
over the pairs of `s`, one over each, and gives zero otherwise. -/
theorem matchedIdem_mul_of (φ : StrandDiagram α) :
    matchedIdem R M s * of φ = if φ.source ∈ matchedChoices M s then of φ else 0 := by
  simp only [matchedIdem_def, sum_mul, idem_mul_of, sum_ite_eq', mem_filter, mem_univ, true_and]
  refine if_congr ?_ rfl rfl
  rw [mem_matchedChoices]
  exact and_congr_right fun h ↦ by rw [← card_image_iff, h, eq_comm]

/-- The coefficients of `I(s) x` are those of `x` at the diagrams whose starting points lie over
the pairs of `s`, one over each, and zero elsewhere. -/
theorem repr_matchedIdem_mul_apply (x : StrandsAlgebra R α) (φ : StrandDiagram α) :
    (basis R α).repr (matchedIdem R M s * x) φ =
      if φ.source ∈ matchedChoices M s then (basis R α).repr x φ else 0 := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [mul_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply]
    split_ifs <;> simp
  | smul_of r ψ =>
    rw [mul_smul_comm, matchedIdem_mul_of]
    by_cases hψφ : ψ = φ
    · subst hψφ
      split_ifs <;> simp
    · split_ifs <;> simp [hψφ]

/-- The coefficient of `I(s)` at the identity diagram of a set `S` of points over `s` is `1`. -/
theorem repr_matchedIdem_apply_idOn {S : Finset α} (hS : S ∈ matchedChoices M s) :
    (basis R α).repr (matchedIdem R M s) (idOn S) = 1 := by
  rw [mem_matchedChoices] at hS
  have hcard : #S = #s := by rw [← hS.1, card_image_of_injOn hS.2]
  simp [repr_matchedIdem_apply, hS.1, hcard]

/-- An element of the matched subalgebra takes the same value at the identity diagrams of any two
sets of points over the same pairs: they differ by moving horizontal strands within matched
pairs. -/
theorem repr_apply_idOn_eq {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R M)
    {S T : Finset α} (hS : S ∈ matchedChoices M s) (hT : T ∈ matchedChoices M s) :
    (basis R α).repr x (idOn S) = (basis R α).repr x (idOn T) := by
  refine repr_eq_of_matchedSetoid hx ?_
  simpa [idOn_addHorizontal] using
    (isMatchedGenerator_idOn_empty M s).matchedSetoid_addHorizontal hS hT

omit [LinearOrder α] in
/-- There is a set of points over a set `s` of pairs: choose one point over each pair. -/
theorem exists_mem_matchedChoices (hs : s ⊆ univ.image M) : ∃ S, S ∈ matchedChoices M s := by
  obtain ⟨S, -, hinj, himage⟩ := exists_subset_injOn_image_eq_of_surjOn (f := M) Set.univ s
    fun b hb ↦ by simpa using hs hb
  exact ⟨S, mem_matchedChoices.2 ⟨himage, hinj⟩⟩

/-- **The corner ring of `I(s)` modulo `F_1`.** An element `x` of the matched subalgebra with
`I(s) x = x` agrees with `c I(s)` modulo the elements with no identity diagram in their support,
where `c` is its coefficient at the identity diagram of any set `S` of points over `s`. -/
theorem sub_smul_matchedIdem_mem_lengthFiltration {R : Type*} [CommRing R]
    {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R M) (hex : matchedIdem R M s * x = x)
    {S : Finset α} (hS : S ∈ matchedChoices M s) :
    x - (basis R α).repr x (idOn S) • matchedIdem R M s ∈ lengthFiltration R 1 := by
  refine mem_lengthFiltration_one_iff.2 fun T ↦ ?_
  rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases hT : T ∈ matchedChoices M s
  · rw [repr_matchedIdem_apply_idOn hT, mul_one, repr_apply_idOn_eq hx hS hT, sub_self]
  · have h0 : (basis R α).repr x (idOn T) = 0 := by
      rw [← hex, repr_matchedIdem_mul_apply, source_idOn]
      simp [hT]
    have h1 : (basis R α).repr (matchedIdem R M s) (idOn T) = 0 := by
      rw [← (isIdempotentElem_matchedIdem M s).eq, repr_matchedIdem_mul_apply, source_idOn]
      simp [hT]
    rw [h0, h1, mul_zero, sub_zero]

/-- **The idempotents of the corner ring of `I(s)`.** When the ground ring has no idempotents
besides `0` and `1`, the only idempotents `x` of the matched subalgebra with `I(s) x = x I(s) = x`
are `0` and `I(s)`. -/
theorem eq_zero_or_eq_matchedIdem_of_isIdempotentElem {R : Type*} [CommRing R]
    (h1 : IsPrimitiveIdempotent (1 : R)) {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R M) (hxx : IsIdempotentElem x) (hex : matchedIdem R M s * x = x)
    (hxe : x * matchedIdem R M s = x) : x = 0 ∨ x = matchedIdem R M s := by
  by_cases hs : s ⊆ univ.image M
  swap
  · left
    rw [← hex, matchedIdem_eq_horizontalCompletion, horizontalCompletion_eq_zero_of_not_subset _ hs,
      zero_mul]
  obtain ⟨S, hS⟩ := exists_mem_matchedChoices hs
  have hn : x - (basis R α).repr x (idOn S) • matchedIdem R M s ∈ lengthFiltration R 1 :=
    sub_smul_matchedIdem_mem_lengthFiltration hx hex hS
  -- Reducing `x² = x` modulo `F_1` shows that the coefficient `c` of `x` at `I(S)` is an
  -- idempotent of `R`, so it is `0` or `1`.
  generalize hc : (basis R α).repr x (idOn S) = c at hn
  have hcc : IsIdempotentElem c := by
    generalize hn' : x - c • matchedIdem R M s = n at hn
    have hx' : x = c • matchedIdem R M s + n := by rw [← hn', add_sub_cancel]
    have h2 : x - (c * c) • matchedIdem R M s =
        c • (matchedIdem R M s * n) + c • (n * matchedIdem R M s) + n * n := by
      conv_lhs => rw [← hxx.eq, hx']
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
        (isIdempotentElem_matchedIdem M s).eq]
      abel
    have hF (y : StrandsAlgebra R α) : y ∈ lengthFiltration R 0 := by simp
    have hsq : x - (c * c) • matchedIdem R M s ∈ lengthFiltration R 1 := by
      rw [h2]
      refine add_mem (add_mem (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)) ?_
      · simpa using mul_mem_lengthFiltration (hF _) hn
      · simpa using mul_mem_lengthFiltration hn (hF _)
      · exact lengthFiltration_antitone (by norm_num) (mul_mem_lengthFiltration hn hn)
    have hdiff := mem_lengthFiltration_one_iff.1 (sub_mem hsq (hn' ▸ hn)) S
    rw [sub_sub_sub_cancel_left, ← sub_smul, map_smul, Finsupp.smul_apply,
      repr_matchedIdem_apply_idOn hS, smul_eq_mul, mul_one, sub_eq_zero] at hdiff
    exact hdiff.symm
  -- Then `x` or `I(s) - x` is an idempotent in `F_1`, hence nilpotent and zero.
  have := h1.nontrivial
  rcases isPrimitiveIdempotent_one_iff.1 h1 c hcc with rfl | rfl
  · rw [zero_smul, sub_zero] at hn
    exact .inl (hxx.eq_zero_of_isNilpotent (isNilpotent_of_mem_lengthFiltration_one hn))
  · rw [one_smul] at hn
    have hsub : IsIdempotentElem (matchedIdem R M s - x) :=
      hxx.sub (isIdempotentElem_matchedIdem M s) hxe hex
    refine .inr (sub_eq_zero.1 (hsub.eq_zero_of_isNilpotent ?_)).symm
    exact isNilpotent_of_mem_lengthFiltration_one (by simpa only [neg_sub] using neg_mem hn)

/-- **The idempotents `I(s)` are primitive.** The idempotent `I(s)` of the matched subalgebra is
primitive exactly when `s` is a set of matched pairs and the ground ring has no idempotents besides
`0` and `1`, as for `𝔽₂`. -/
theorem isPrimitiveIdempotent_matchedIdem_iff {R : Type*} [CommRing R] :
    IsPrimitiveIdempotent
        (⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩ : matchedSubalgebra R M) ↔
      IsPrimitiveIdempotent (1 : R) ∧ s ⊆ univ.image M := by
  set e : matchedSubalgebra R M := ⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩
  have he : IsIdempotentElem e := Subtype.ext (isIdempotentElem_matchedIdem M s)
  constructor
  · intro hprim
    have hs : s ⊆ univ.image M := by
      by_contra hs
      exact hprim.ne_zero (Subtype.ext ((matchedIdem_eq_horizontalCompletion M s).trans
        (horizontalCompletion_eq_zero_of_not_subset _ hs)))
    obtain ⟨S, hS⟩ := exists_mem_matchedChoices hs
    have : Nontrivial R := by
      refine (subsingleton_or_nontrivial R).resolve_left fun _ ↦ hprim.ne_zero ?_
      exact Subtype.ext ((basis R α).repr.injective (Subsingleton.elim _ _))
    refine ⟨isPrimitiveIdempotent_one_iff.2 fun r hr ↦ ?_, hs⟩
    -- `r I(s)` is an idempotent of the corner ring of `I(s)`, so it is `0` or `I(s)`.
    have hre : IsIdempotentElem (r • e) := by
      rw [IsIdempotentElem, smul_mul_smul_comm, hr.eq, he.eq]
    have key := hprim.eq_zero_or_eq hre (by rw [mul_smul_comm, he.eq]) (by rw [smul_mul_assoc,
      he.eq])
    have hcoeff : (basis R α).repr ((r • e : matchedSubalgebra R M) : StrandsAlgebra R α)
        (idOn S) = r := by
      rw [NonUnitalSubalgebra.coe_smul, map_smul, Finsupp.smul_apply,
        repr_matchedIdem_apply_idOn hS, smul_eq_mul, mul_one]
    refine key.imp (fun h ↦ ?_) fun h ↦ ?_ <;> rw [← hcoeff, h]
    · simp
    · exact repr_matchedIdem_apply_idOn hS
  · rintro ⟨h1, hs⟩
    have := h1.nontrivial
    obtain ⟨S, hS⟩ := exists_mem_matchedChoices hs
    refine isPrimitiveIdempotent_of_eq_zero_or_eq he (fun he0 ↦ ?_) fun f hf hef hfe ↦ ?_
    · have := repr_matchedIdem_apply_idOn (R := R) hS
      rw [show matchedIdem R M s = 0 from congrArg Subtype.val he0] at this
      simp at this
    refine (eq_zero_or_eq_matchedIdem_of_isIdempotentElem h1 f.2 (congrArg Subtype.val hf.eq)
      (congrArg Subtype.val hef) (congrArg Subtype.val hfe)).imp Subtype.ext Subtype.ext

/-- The idempotents `I(s)` over the sets `s` of matched pairs form a **complete family of
orthogonal idempotents** of the matched subalgebra: they are pairwise orthogonal and sum to its
unit. -/
theorem completeOrthogonalIdempotents_matchedIdem :
    CompleteOrthogonalIdempotents fun s : (univ.image M).powerset ↦
      (⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩ : matchedSubalgebra R M) := by
  refine CompleteOrthogonalIdempotents.iff_ortho_complete.2 ⟨fun s t hst ↦ ?_, ?_⟩
  · refine Subtype.ext ?_
    simp [Subtype.coe_ne_coe.2 hst]
  · refine Subtype.ext ?_
    simp only [AddSubmonoidClass.coe_finsetSum, coe_matchedSubalgebra_one, matchedOne_def]
    exact sum_coe_sort _ fun s ↦ matchedIdem R M s

end Primitive

end StrandsAlgebra

end TauCeti
