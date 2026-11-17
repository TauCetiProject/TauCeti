/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.Algebra.Homology.SquareZero
import TauCeti.LinearAlgebra.End.Nilpotent

/-!
# Slash homology of `p`-differential modules

A linear endomorphism `d` of a module `M` satisfying `d ^ p = 0` admits `p - 1` **slash homology**
groups indexed by `0 ≤ j ≤ p - 2`:

`H^{/j}(M) = ker(d ^ (j + 1)) / (im(d ^ (p - j - 1)) + ker(d ^ j))`.

At `p = 2` and `j = 0`, `SlashHomology 2 d 0` recovers ordinary square-zero homology `ker d / im d`
(`SlashHomology.twoZeroEquivHomology`). Intertwining linear maps act functorially on slash
homology, and `p`-homotopic maps (`f - g = ∑_{i < p} d_N ^ i ∘ h ∘ d_M ^ (p - 1 - i)`) induce equal
maps on every `SlashHomology` group.

Vanishing of all `p - 1` slash homology groups characterizes the exact filtrations
`ker(d ^ m) = im(d ^ (p - m))` for `0 ≤ m ≤ p`. Over a division ring, vanishing of all slash
homology groups produces a monomial basis `(i, r) ↦ d ^ r (v i)` of `M` without assuming finite
dimensionality (`SlashHomology.exists_basis_pow_of_forall_subsingleton`). Independently, for any
finite-dimensional `p`-complex (`d ^ p = 0`) over a division ring, Khovanov–Qi's dimension
decomposition gives `dim M = p · dim(im(d ^ (p - 1))) + ∑_{j = 0}^{p - 2} dim H^{/j}(M)`
(`SlashHomology.finrank_eq_mul_finrank_range_pow_add_sum`).

## Main definitions and results

* `TauCeti.SlashHomology`, `boundaries`, `π`, `map`, `equiv`, `prodEquiv`,
  `twoZeroEquivHomology`, `zeroDiffZeroEquiv`.
* `TauCeti.SlashHomology.nullHomotopicMap`, `IsPHomotopic`, `map_nullHomotopicMap`,
  `map_eq_of_isPHomotopic`: `p`-chain homotopy invariance of slash homology.
* `TauCeti.SlashHomology.forall_subsingleton_iff_ker_pow_eq_range_pow`,
  `exists_basis_pow_of_forall_subsingleton`, `finrank_eq_mul_finrank_range_pow_add_sum`.

## References

* M. Kapranov, *On the q-analog of homological algebra*, arXiv:q-alg/9611005, 1996.
* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications **25** (2016), no. 3, 1640006.
* M. Khovanov and Y. Qi, *An approach to categorification of some small quantum groups*,
  Quantum Topol. **6** (2015), 185–311, §2 (slash homology and equation (20)).
-/

public section

namespace TauCeti

section Semiring

variable {R M N P : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

namespace SlashHomology

/-- The submodule of `ker(d ^ (j + 1))` cut out by `im(d ^ (p - j - 1)) ⊔ ker(d ^ j)`. -/
abbrev boundaries (p : ℕ) (d : M →ₗ[R] M) (j : ℕ) :
    Submodule R (LinearMap.ker (d ^ (j + 1))) :=
  (LinearMap.range (d ^ (p - j - 1)) ⊔ LinearMap.ker (d ^ j)).comap
    (LinearMap.ker (d ^ (j + 1))).subtype

/-- Membership in `boundaries` is membership of the underlying vector in
`im(d ^ (p - j - 1)) ⊔ ker(d ^ j)`. -/
theorem mem_boundaries {p : ℕ} {d : M →ₗ[R] M} {j : ℕ} {z : LinearMap.ker (d ^ (j + 1))} :
    z ∈ boundaries p d j ↔ (z : M) ∈ LinearMap.range (d ^ (p - j - 1)) ⊔ LinearMap.ker (d ^ j) :=
  Iff.rfl

/-- When `d ^ p = 0`, the image `im(d ^ (p - j - 1))` lies inside `ker(d ^ (j + 1))`. -/
theorem range_pow_le_ker_pow {p : ℕ} {d : M →ₗ[R] M} (hd : d ^ p = 0) (j : ℕ) :
    LinearMap.range (d ^ (p - j - 1)) ≤ LinearMap.ker (d ^ (j + 1)) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker, ← mul_apply_eq_comp, ← pow_add,
    pow_eq_zero_of_le (by omega : p ≤ j + 1 + (p - j - 1)) hd, LinearMap.zero_apply]

/-- **Denominator containment.** When `d ^ p = 0`, the denominator
`im(d ^ (p - j - 1)) ⊔ ker(d ^ j)` of `SlashHomology p d j` is contained in `ker(d ^ (j + 1))`. -/
theorem range_sup_ker_le_ker {p : ℕ} {d : M →ₗ[R] M} (hd : d ^ p = 0) (j : ℕ) :
    LinearMap.range (d ^ (p - j - 1)) ⊔ LinearMap.ker (d ^ j) ≤ LinearMap.ker (d ^ (j + 1)) :=
  sup_le (range_pow_le_ker_pow hd j) ((LinearMap.iterateKer d).monotone (Nat.le_succ j))

/-- The `p`-null-homotopic map `∑_{i = 0}^{p - 1} e ^ i ∘ h ∘ d ^ (p - 1 - i)` associated to an
arbitrary `R`-linear operator `h : M → N`. -/
def nullHomotopicMap (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (h : M →ₗ[R] N) : M →ₗ[R] N :=
  ∑ i ∈ Finset.range p, (e ^ i) ∘ₗ h ∘ₗ (d ^ (p - 1 - i))

/-- Definitional formula for `nullHomotopicMap`. -/
theorem nullHomotopicMap_def (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (h : M →ₗ[R] N) :
    nullHomotopicMap p d e h = ∑ i ∈ Finset.range p, (e ^ i) ∘ₗ h ∘ₗ (d ^ (p - 1 - i)) :=
  (rfl)

/-- Pointwise evaluation of `nullHomotopicMap`. -/
theorem nullHomotopicMap_apply (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (h : M →ₗ[R] N) (m : M) :
    nullHomotopicMap p d e h m = ∑ i ∈ Finset.range p, (e ^ i) (h ((d ^ (p - 1 - i)) m)) := by
  simp [nullHomotopicMap, LinearMap.sum_apply]

/-- `nullHomotopicMap` of the zero homotopy is zero. -/
@[simp]
theorem nullHomotopicMap_zero (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) :
    nullHomotopicMap p d e 0 = 0 := by
  simp [nullHomotopicMap]

/-- `nullHomotopicMap` is additive in the contracting homotopy. -/
@[simp]
theorem nullHomotopicMap_add (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (h₁ h₂ : M →ₗ[R] N) :
    nullHomotopicMap p d e (h₁ + h₂) =
      nullHomotopicMap p d e h₁ + nullHomotopicMap p d e h₂ := by
  simp [nullHomotopicMap, LinearMap.comp_add, LinearMap.add_comp, Finset.sum_add_distrib]

/-- Post-composing `nullHomotopicMap` with an intertwining map `g` (`g ∘ e = q ∘ g`) shifts `g`
inside the contracting homotopy. -/
theorem comp_nullHomotopicMap_of_comp_eq (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N}
    {q : P →ₗ[R] P} (g : N →ₗ[R] P) (hg : g ∘ₗ e = q ∘ₗ g) (h : M →ₗ[R] N) :
    g ∘ₗ nullHomotopicMap p d e h = nullHomotopicMap p d q (g ∘ₗ h) := by
  ext m
  simp only [LinearMap.comp_apply, nullHomotopicMap_apply, _root_.map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simpa using LinearMap.congr_fun
    (Module.End.commute_pow_left_of_commute hg.symm i).symm (h ((d ^ (p - 1 - i)) m))

/-- Pre-composing `nullHomotopicMap` with an intertwining map `f` (`f ∘ c = d ∘ f`) shifts `f`
inside the contracting homotopy. -/
theorem nullHomotopicMap_comp_of_comp_eq (p : ℕ) {c : P →ₗ[R] P} {d : M →ₗ[R] M}
    {e : N →ₗ[R] N} (f : P →ₗ[R] M) (hf : f ∘ₗ c = d ∘ₗ f) (h : M →ₗ[R] N) :
    nullHomotopicMap p d e h ∘ₗ f = nullHomotopicMap p c e (h ∘ₗ f) := by
  ext m
  simp only [LinearMap.comp_apply, nullHomotopicMap_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show (d ^ (p - 1 - i)) (f m) = f ((c ^ (p - 1 - i)) m) from
    (LinearMap.congr_fun
      (Module.End.commute_pow_left_of_commute hf.symm (p - 1 - i)).symm m).symm]

/-- When `d ^ p = 0` and `e ^ p = 0`, every `nullHomotopicMap p d e h` intertwines `d` and `e`. -/
theorem nullHomotopicMap_comm {p : ℕ} {d : M →ₗ[R] M} {e : N →ₗ[R] N}
    (hd : d ^ p = 0) (he : e ^ p = 0) (h : M →ₗ[R] N) :
    nullHomotopicMap p d e h ∘ₗ d = e ∘ₗ nullHomotopicMap p d e h := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [nullHomotopicMap]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  ext m
  simp only [LinearMap.comp_apply, nullHomotopicMap_apply, _root_.map_sum]
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have hleft : (e ^ 0) (h ((d ^ (q + 1 - 1 - 0)) (d m))) = 0 := by
    have hpow : (d ^ q) (d m) = 0 := by
      rw [← mul_apply_eq_comp, ← pow_succ, hd, LinearMap.zero_apply]
    simp [hpow]
  have hright : e ((e ^ q) (h ((d ^ (q + 1 - 1 - q)) m))) = 0 := by
    rw [← mul_apply_eq_comp, ← pow_succ', he, LinearMap.zero_apply]
  rw [hleft, hright, add_zero, add_zero]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  have hd_eq : (d ^ (q + 1 - 1 - (i + 1))) (d m) = (d ^ (q + 1 - 1 - i)) m := by
    simp only [Nat.add_sub_cancel]
    rw [show q - i = (q - 1 - i) + 1 by omega, pow_succ, mul_apply_eq_comp]
    congr 2; omega
  rw [hd_eq, ← mul_apply_eq_comp, ← pow_succ']

/-- Every `nullHomotopicMap` carries `ker(d ^ (j + 1))` into `im(e ^ (p - j - 1))`. -/
theorem nullHomotopicMap_mem_range {p : ℕ} {d : M →ₗ[R] M} (e : N →ₗ[R] N)
    (h : M →ₗ[R] N) (j : ℕ) {z : M} (hz : z ∈ LinearMap.ker (d ^ (j + 1))) :
    nullHomotopicMap p d e h z ∈ LinearMap.range (e ^ (p - j - 1)) := by
  rw [nullHomotopicMap_apply]
  refine Submodule.sum_mem _ fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rcases le_or_gt (p - j - 1) i with hle | hlt
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [pow_add, mul_apply_eq_comp]
    exact LinearMap.mem_range_self _ _
  · obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (by omega : j + 1 ≤ p - 1 - i)
    rw [hr, add_comm, pow_add, mul_apply_eq_comp, LinearMap.mem_ker.mp hz,
      _root_.map_zero, _root_.map_zero, _root_.map_zero]
    exact zero_mem _

private theorem subsingleton_of_pow_zero_eq_zero {d : M →ₗ[R] M} (hd : d ^ 0 = 0) :
    Subsingleton M :=
  Subsingleton.intro fun x y ↦ by
    have hx : x = 0 := by simpa [Module.End.one_eq_id] using LinearMap.congr_fun hd x
    have hy : y = 0 := by simpa [Module.End.one_eq_id] using LinearMap.congr_fun hd y
    rw [hx, hy]

end SlashHomology

end Semiring

section NullHomotopicNeg

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- `nullHomotopicMap` commutes with negation of the contracting homotopy. -/
@[simp]
theorem SlashHomology.nullHomotopicMap_neg (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N)
    (h : M →ₗ[R] N) :
    SlashHomology.nullHomotopicMap p d e (-h) = -SlashHomology.nullHomotopicMap p d e h := by
  simp [SlashHomology.nullHomotopicMap, LinearMap.comp_neg, LinearMap.neg_comp]

end NullHomotopicNeg

section Ring

variable {R M N P : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The slash homology `H^{/j}(M) = ker(d ^ (j + 1)) / (im(d ^ (p - j - 1)) + ker(d ^ j))` of a
linear endomorphism `d`, realized as a quotient of `ker(d ^ (j + 1))` (Khovanov–Qi, §2). -/
abbrev SlashHomology (p : ℕ) (d : M →ₗ[R] M) (j : ℕ) : Type _ :=
  LinearMap.ker (d ^ (j + 1)) ⧸
    (LinearMap.range (d ^ (p - j - 1)) ⊔ LinearMap.ker (d ^ j)).comap
      (LinearMap.ker (d ^ (j + 1))).subtype

namespace SlashHomology

/-- The quotient map sending a slash cycle `z ∈ ker(d ^ (j + 1))` to its slash homology class. -/
noncomputable def π (p : ℕ) (d : M →ₗ[R] M) (j : ℕ) :
    LinearMap.ker (d ^ (j + 1)) →ₗ[R] SlashHomology p d j :=
  (boundaries p d j).mkQ

/-- Evaluation of `SlashHomology.π` on a slash cycle. -/
@[simp]
theorem π_apply (p : ℕ) (d : M →ₗ[R] M) (j : ℕ) (z : LinearMap.ker (d ^ (j + 1))) :
    π p d j z = Submodule.Quotient.mk z :=
  (rfl)

/-- Every slash homology class is represented by a slash cycle in `ker(d ^ (j + 1))`. -/
theorem π_surjective (p : ℕ) (d : M →ₗ[R] M) (j : ℕ) : Function.Surjective (π p d j) :=
  Submodule.mkQ_surjective _

/-- A slash cycle represents the zero class iff it lies in `im(d ^ (p - j - 1)) ⊔ ker(d ^ j)`. -/
theorem π_eq_zero_iff {p : ℕ} {d : M →ₗ[R] M} {j : ℕ} (z : LinearMap.ker (d ^ (j + 1))) :
    π p d j z = 0 ↔ (z : M) ∈ LinearMap.range (d ^ (p - j - 1)) ⊔ LinearMap.ker (d ^ j) :=
  Submodule.Quotient.mk_eq_zero _

/-- `SlashHomology p d j` is a subsingleton iff `ker(d ^ (j + 1))` is contained in
`im(d ^ (p - j - 1)) ⊔ ker(d ^ j)`. -/
theorem subsingleton_iff {p : ℕ} {d : M →ₗ[R] M} {j : ℕ} :
    Subsingleton (SlashHomology p d j) ↔
      LinearMap.ker (d ^ (j + 1)) ≤ LinearMap.range (d ^ (p - j - 1)) ⊔ LinearMap.ker (d ^ j) := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  exact ⟨fun h x hx ↦ h (Submodule.mem_top (x := ⟨x, hx⟩)), fun h ⟨x, hx⟩ _ ↦ h hx⟩

/-- When `d ^ p = 0`, `SlashHomology p d j` vanishes iff
`ker(d ^ (j + 1)) = im(d ^ (p - j - 1)) ⊔ ker(d ^ j)`. -/
theorem subsingleton_iff_ker_eq {p : ℕ} {d : M →ₗ[R] M} (hd : d ^ p = 0) (j : ℕ) :
    Subsingleton (SlashHomology p d j) ↔
      LinearMap.ker (d ^ (j + 1)) = LinearMap.range (d ^ (p - j - 1)) ⊔ LinearMap.ker (d ^ j) :=
  subsingleton_iff.trans ⟨fun h ↦ le_antisymm h (range_sup_ker_le_ker hd j), le_of_eq⟩

/-! ### Functoriality and products -/

/-- A linear map `f : M → N` intertwining `d` and `e` (`f ∘ d = e ∘ f`) induces a linear map on
slash homology in every degree `j`. -/
noncomputable def map (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f : M →ₗ[R] N)
    (hf : f ∘ₗ d = e ∘ₗ f) (j : ℕ) : SlashHomology p d j →ₗ[R] SlashHomology p e j :=
  (boundaries p d j).mapQ (boundaries p e j)
    (f.restrict fun _ ↦ LinearMap.map_mem_ker_of_comp_eq f
      (Module.End.commute_pow_left_of_commute hf.symm (j + 1)).symm) <| by
    rintro z hz
    rw [Submodule.mem_comap, mem_boundaries, LinearMap.coe_restrict_apply]
    rcases Submodule.mem_sup.mp (mem_boundaries.mp hz) with ⟨_, ⟨x, rfl⟩, _, hv, huv⟩
    rw [← huv, _root_.map_add]
    refine Submodule.add_mem_sup ⟨f x, ?_⟩ (LinearMap.map_mem_ker_of_comp_eq f
      (Module.End.commute_pow_left_of_commute hf.symm j).symm hv)
    simpa using (LinearMap.congr_fun
      (Module.End.commute_pow_left_of_commute hf.symm (p - j - 1)).symm x).symm

/-- `SlashHomology.map` sends the class of a slash cycle `z` to the class of `f z`. -/
@[simp]
theorem map_mk (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f : M →ₗ[R] N)
    (hf : f ∘ₗ d = e ∘ₗ f) (j : ℕ) (z : LinearMap.ker (d ^ (j + 1))) :
    map p f hf j (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨f z, LinearMap.map_mem_ker_of_comp_eq f
        (Module.End.commute_pow_left_of_commute hf.symm (j + 1)).symm z.2⟩ :=
  (rfl)

/-- The identity map induces the identity on slash homology. -/
@[simp]
theorem map_id (p : ℕ) (d : M →ₗ[R] M) (j : ℕ) :
    map p LinearMap.id (by simp : LinearMap.id ∘ₗ d = d ∘ₗ LinearMap.id) j = LinearMap.id := by
  ext z; simp

/-- The zero map induces the zero map on slash homology. -/
@[simp]
theorem map_zero (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (j : ℕ) :
    map p (0 : M →ₗ[R] N) (by simp : (0 : M →ₗ[R] N) ∘ₗ d = e ∘ₗ 0) j = 0 := by
  ext z; simp

/-- `SlashHomology.map` is additive in the intertwining map. -/
@[simp]
theorem map_add (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f g : M →ₗ[R] N)
    (hf : f ∘ₗ d = e ∘ₗ f) (hg : g ∘ₗ d = e ∘ₗ g) (j : ℕ) :
    map p (f + g) (by rw [LinearMap.add_comp, LinearMap.comp_add, hf, hg]) j =
      map p f hf j + map p g hg j := by
  ext z; simp [← Submodule.Quotient.mk_add]

/-- `SlashHomology.map` commutes with negation. -/
@[simp]
theorem map_neg (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f : M →ₗ[R] N)
    (hf : f ∘ₗ d = e ∘ₗ f) (j : ℕ) :
    map p (-f) (by rw [LinearMap.neg_comp, LinearMap.comp_neg, hf]) j = -map p f hf j := by
  ext z; simp [← Submodule.Quotient.mk_neg, Submodule.Quotient.eq]

/-- `SlashHomology.map` commutes with subtraction. -/
@[simp]
theorem map_sub (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f g : M →ₗ[R] N)
    (hf : f ∘ₗ d = e ∘ₗ f) (hg : g ∘ₗ d = e ∘ₗ g) (j : ℕ) :
    map p (f - g) (by rw [LinearMap.sub_comp, LinearMap.comp_sub, hf, hg]) j =
      map p f hf j - map p g hg j := by
  ext z; simp [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]

/-- `SlashHomology.map` preserves composition of intertwining maps. -/
theorem map_comp (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} {q : P →ₗ[R] P}
    (g : N →ₗ[R] P) (f : M →ₗ[R] N) (hf : f ∘ₗ d = e ∘ₗ f) (hg : g ∘ₗ e = q ∘ₗ g) (j : ℕ) :
    map p (g ∘ₗ f)
        (by rw [LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc, hg, LinearMap.comp_assoc]) j =
      map p g hg j ∘ₗ map p f hf j := by
  ext z; simp

/-- Simp-oriented composition law for `SlashHomology.map`. -/
@[simp]
theorem map_comp_map (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} {q : P →ₗ[R] P}
    (g : N →ₗ[R] P) (f : M →ₗ[R] N) (hf : f ∘ₗ d = e ∘ₗ f) (hg : g ∘ₗ e = q ∘ₗ g) (j : ℕ) :
    map p g hg j ∘ₗ map p f hf j =
      map p (g ∘ₗ f)
        (by rw [LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc, hg, LinearMap.comp_assoc]) j :=
  (map_comp p g f hf hg j).symm

/-- A linear equivalence intertwining `d` and `e` induces a linear equivalence on slash
homology. -/
noncomputable def equiv (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f : M ≃ₗ[R] N)
    (hf : f.toLinearMap ∘ₗ d = e ∘ₗ f.toLinearMap) (j : ℕ) :
    SlashHomology p d j ≃ₗ[R] SlashHomology p e j :=
  have hf' : f.symm.toLinearMap ∘ₗ e = d ∘ₗ f.symm.toLinearMap := by
    ext y; apply f.injective; simpa using (LinearMap.congr_fun hf (f.symm y)).symm
  LinearEquiv.ofLinearMap (map p f.toLinearMap hf j) (map p f.symm.toLinearMap hf' j)
    (by ext z; simp) (by ext z; simp)

/-- `SlashHomology.equiv` acts on cycle classes via `SlashHomology.map`. -/
@[simp]
theorem equiv_mk (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f : M ≃ₗ[R] N)
    (hf : f.toLinearMap ∘ₗ d = e ∘ₗ f.toLinearMap) (j : ℕ) (z : LinearMap.ker (d ^ (j + 1))) :
    equiv p f hf j (Submodule.Quotient.mk z) = map p f.toLinearMap hf j (Submodule.Quotient.mk z) :=
  (rfl)

/-- Slash homology of a product endomorphism `d.prodMap e` is the product of the slash
homologies. -/
noncomputable def prodEquiv (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (j : ℕ) :
    SlashHomology p (d.prodMap e) j ≃ₗ[R] SlashHomology p d j × SlashHomology p e j :=
  LinearEquiv.ofLinearMap
    ((map p (LinearMap.fst R M N) (by ext <;> simp) j).prod
      (map p (LinearMap.snd R M N) (by ext <;> simp) j))
    ((map p (LinearMap.inl R M N) (by ext <;> simp) j).coprod
      (map p (LinearMap.inr R M N) (by ext <;> simp) j))
    (LinearMap.ext fun ⟨c₁, c₂⟩ ↦ by
      obtain ⟨z₁, rfl⟩ := π_surjective p d j c₁
      obtain ⟨z₂, rfl⟩ := π_surjective p e j c₂
      simp)
    (by
      ext z
      have hdecomp :
          LinearMap.inl R M N ∘ₗ LinearMap.fst R M N +
            LinearMap.inr R M N ∘ₗ LinearMap.snd R M N = LinearMap.id := by ext <;> simp
      have hsum := map_add p (d := d.prodMap e) (e := d.prodMap e)
        (LinearMap.inl R M N ∘ₗ LinearMap.fst R M N)
        (LinearMap.inr R M N ∘ₗ LinearMap.snd R M N)
        (by ext <;> simp) (by ext <;> simp) j
      simpa [← map_comp_map, hdecomp] using
        LinearMap.congr_fun hsum.symm (Submodule.Quotient.mk z))

/-- `SlashHomology.prodEquiv` sends a cycle class to its two component classes. -/
@[simp]
theorem prodEquiv_mk (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (j : ℕ)
    (z : LinearMap.ker ((d.prodMap e) ^ (j + 1))) :
    prodEquiv p d e j (Submodule.Quotient.mk z) =
      (Submodule.Quotient.mk ⟨z.1.1, LinearMap.map_mem_ker_of_comp_eq (LinearMap.fst R M N)
          (Module.End.commute_pow_left_of_commute (by ext <;> simp) (j + 1)).symm z.2⟩,
        Submodule.Quotient.mk ⟨z.1.2, LinearMap.map_mem_ker_of_comp_eq (LinearMap.snd R M N)
          (Module.End.commute_pow_left_of_commute (by ext <;> simp) (j + 1)).symm z.2⟩) := by
  simp [prodEquiv]

/-- The inverse of `SlashHomology.prodEquiv` sends a pair of cycle classes to their product
class. -/
@[simp]
theorem prodEquiv_symm_mk (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (j : ℕ)
    (x : LinearMap.ker (d ^ (j + 1))) (y : LinearMap.ker (e ^ (j + 1))) :
    (prodEquiv p d e j).symm (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨((x : M), (y : N)), by
        have hinl : (d.prodMap e) ∘ₗ LinearMap.inl R M N = LinearMap.inl R M N ∘ₗ d := by
          ext <;> simp
        have hinr : (d.prodMap e) ∘ₗ LinearMap.inr R M N = LinearMap.inr R M N ∘ₗ e := by
          ext <;> simp
        have hx := LinearMap.map_mem_ker_of_comp_eq (LinearMap.inl R M N)
          (Module.End.commute_pow_left_of_commute hinl (j + 1)).symm x.2
        have hy := LinearMap.map_mem_ker_of_comp_eq (LinearMap.inr R M N)
          (Module.End.commute_pow_left_of_commute hinr (j + 1)).symm y.2
        simpa using add_mem hx hy⟩ := by
  apply (prodEquiv p d e j).injective
  simp only [LinearEquiv.apply_symm_apply, prodEquiv_mk]

/-! ### Comparison with ordinary homology at `p = 2` -/

/-- **Comparison with square-zero homology.** At `p = 2` and `j = 0`, slash homology of a
square-zero endomorphism `d` (`d ∘ d = 0`) is canonically isomorphic to `d.homology hd`. -/
noncomputable def twoZeroEquivHomology (d : M →ₗ[R] M) (hd : d ∘ₗ d = 0) :
    SlashHomology 2 d 0 ≃ₗ[R] d.homology hd :=
  Submodule.Quotient.equiv (boundaries 2 d 0) d.boundariesInKer (LinearEquiv.ofEq _ _ (by simp))
    (by ext z; simp [Module.End.one_eq_id])

/-- `twoZeroEquivHomology` sends the slash-homology class of a cycle `z` to its ordinary homology
class. -/
@[simp]
theorem twoZeroEquivHomology_mk (d : M →ₗ[R] M) (hd : d ∘ₗ d = 0)
    (z : LinearMap.ker (d ^ (0 + 1))) :
    twoZeroEquivHomology d hd (Submodule.Quotient.mk z) =
      d.homologyπ hd ⟨z.1, by simpa using z.2⟩ := by
  simp only [twoZeroEquivHomology, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    LinearMap.homologyπ_apply]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (LinearEquiv.coe_ofEq_apply _ z))

/-! ### `p`-chain homotopy invariance -/

/-- **A `p`-null-homotopic map induces zero on all slash homology groups.** -/
@[simp]
theorem map_nullHomotopicMap {p : ℕ} {d : M →ₗ[R] M} {e : N →ₗ[R] N}
    (hd : d ^ p = 0) (he : e ^ p = 0) (h : M →ₗ[R] N) (j : ℕ) :
    map p (nullHomotopicMap p d e h) (nullHomotopicMap_comm hd he h) j = 0 := by
  ext z
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, map_mk, LinearMap.zero_apply]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.mem_sup_left (nullHomotopicMap_mem_range e h j z.2))

/-- Two linear maps `f, g : M → N` are **`p`-homotopic** when their difference is of the form
`∑_{i = 0}^{p - 1} e ^ i ∘ h ∘ d ^ (p - 1 - i)` for some `R`-linear `h : M → N`. -/
def IsPHomotopic (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (f g : M →ₗ[R] N) : Prop :=
  ∃ h : M →ₗ[R] N, f - g = nullHomotopicMap p d e h

/-- Characterization of `IsPHomotopic` in terms of `nullHomotopicMap`. -/
theorem isPHomotopic_iff (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (f g : M →ₗ[R] N) :
    IsPHomotopic p d e f g ↔ ∃ h : M →ₗ[R] N, f - g = nullHomotopicMap p d e h :=
  Iff.rfl

/-- `IsPHomotopic` is reflexive. -/
@[refl]
theorem IsPHomotopic.refl (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (f : M →ₗ[R] N) :
    IsPHomotopic p d e f f :=
  ⟨0, by simp⟩

/-- `IsPHomotopic` is symmetric. -/
@[symm]
theorem IsPHomotopic.symm {p : ℕ} {d : M →ₗ[R] M} {e : N →ₗ[R] N} {f g : M →ₗ[R] N}
    (hfg : IsPHomotopic p d e f g) : IsPHomotopic p d e g f :=
  let ⟨h, hh⟩ := hfg; ⟨-h, by rw [← neg_sub, hh, nullHomotopicMap_neg]⟩

/-- `IsPHomotopic` is transitive. -/
@[trans]
theorem IsPHomotopic.trans {p : ℕ} {d : M →ₗ[R] M} {e : N →ₗ[R] N} {f g k : M →ₗ[R] N}
    (hfg : IsPHomotopic p d e f g) (hgk : IsPHomotopic p d e g k) :
    IsPHomotopic p d e f k :=
  let ⟨h₁, hh₁⟩ := hfg; let ⟨h₂, hh₂⟩ := hgk
  ⟨h₁ + h₂, by rw [← sub_add_sub_cancel f g k, hh₁, hh₂, nullHomotopicMap_add]⟩

/-- **Homotopy invariance of slash homology.** Two `p`-homotopic intertwining maps between
`p`-differentials induce the same map on every slash homology group. -/
theorem map_eq_of_isPHomotopic {p : ℕ} {d : M →ₗ[R] M} {e : N →ₗ[R] N}
    (hd : d ^ p = 0) (he : e ^ p = 0) {f g : M →ₗ[R] N}
    (hf : f ∘ₗ d = e ∘ₗ f) (hg : g ∘ₗ d = e ∘ₗ g) (hfg : IsPHomotopic p d e f g) (j : ℕ) :
    map p f hf j = map p g hg j := by
  obtain ⟨h, hh⟩ := hfg
  rw [← sub_eq_zero, ← map_sub p f g hf hg j]
  have hcongr :
      map p (f - g) (by rw [LinearMap.sub_comp, LinearMap.comp_sub, hf, hg]) j =
        map p (nullHomotopicMap p d e h) (nullHomotopicMap_comm hd he h) j := by congr! 1
  rw [hcongr, map_nullHomotopicMap hd he h j]

/-! ### Zero differential -/

/-- For `2 ≤ p`, the `0`-th slash homology of the zero differential on `M` is canonically
isomorphic to `M`. -/
noncomputable def zeroDiffZeroEquiv {p : ℕ} (hp : 2 ≤ p) :
    SlashHomology p (0 : M →ₗ[R] M) 0 ≃ₗ[R] M := by
  have hpos : p - 1 ≠ 0 := by omega
  have hbot : boundaries p (0 : M →ₗ[R] M) 0 = ⊥ := by
    ext z; simp [zero_pow hpos, Module.End.one_eq_id]
  exact (Submodule.quotEquivOfEqBot _ hbot).trans
    ((LinearEquiv.ofEq _ ⊤ (by simp)).trans Submodule.topEquiv)

/-- `zeroDiffZeroEquiv` sends the class of a cycle `z` to its underlying vector. -/
@[simp]
theorem zeroDiffZeroEquiv_mk {p : ℕ} (hp : 2 ≤ p)
    (z : LinearMap.ker ((0 : M →ₗ[R] M) ^ (0 + 1))) :
    zeroDiffZeroEquiv (R := R) (M := M) hp (Submodule.Quotient.mk z) = z := by
  simp [zeroDiffZeroEquiv]

/-- The inverse of `zeroDiffZeroEquiv` sends `m : M` to its slash-homology class in degree `0`. -/
@[simp]
theorem zeroDiffZeroEquiv_symm_apply {p : ℕ} (hp : 2 ≤ p) (m : M) :
    (zeroDiffZeroEquiv (R := R) (M := M) hp).symm m = Submodule.Quotient.mk ⟨m, by simp⟩ := by
  apply (zeroDiffZeroEquiv (R := R) (M := M) hp).injective; simp

/-- In positive degree `0 < j`, the slash homology of the zero differential vanishes. -/
theorem subsingleton_zero_of_pos {p j : ℕ} (hj : 0 < j) :
    Subsingleton (SlashHomology p (0 : M →ₗ[R] M) j) :=
  subsingleton_iff.mpr fun _ _ ↦ Submodule.mem_sup_right (by simp [zero_pow hj.ne'])

/-- On a nonzero module with zero differential, the identity map is never `p`-null-homotopic for
`2 ≤ p`. -/
theorem not_isPHomotopic_zero_id_zero_of_two_le [Nontrivial M] {p : ℕ} (hp : 2 ≤ p) :
    ¬ IsPHomotopic p (0 : M →ₗ[R] M) (0 : M →ₗ[R] M) LinearMap.id 0 := by
  rintro ⟨h, hh⟩
  have hzero : nullHomotopicMap p (0 : M →ₗ[R] M) (0 : M →ₗ[R] M) h = 0 := by
    rw [nullHomotopicMap_def]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [zero_pow (by omega : p - 1 ≠ 0)]
    · simp [zero_pow hi0.ne']
  rw [sub_zero, hzero] at hh
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  exact hx (by simpa using LinearMap.congr_fun hh x)

/-! ### Characterization of vanishing slash homology -/

/-- **Exact-filtration criterion.** When `d ^ p = 0`, all slash homology groups
`SlashHomology p d j` for `j + 1 < p` vanish iff `ker(d ^ m) = im(d ^ (p - m))` for every
`m ≤ p`. -/
theorem forall_subsingleton_iff_ker_pow_eq_range_pow {p : ℕ} {d : M →ₗ[R] M} (hd : d ^ p = 0) :
    (∀ j, j + 1 < p → Subsingleton (SlashHomology p d j)) ↔
      ∀ m ≤ p, LinearMap.ker (d ^ m) = LinearMap.range (d ^ (p - m)) := by
  constructor
  · intro h m hm
    induction m with
    | zero => simp [Module.End.one_eq_id, hd]
    | succ j ih =>
      rcases eq_or_lt_of_le hm with rfl | hlt
      · simp [hd, Module.End.one_eq_id]
      · have hle_range : LinearMap.range (d ^ (p - j)) ≤ LinearMap.range (d ^ (p - j - 1)) :=
          (LinearMap.iterateRange d).monotone (by omega : p - j - 1 ≤ p - j)
        rw [(subsingleton_iff_ker_eq hd j).mp (h j hlt), ih (by omega),
          sup_of_le_left hle_range, Nat.sub_sub]
  · intro h j hj
    rw [subsingleton_iff, h (j + 1) (by omega), Nat.sub_sub]
    exact le_sup_left

/-- Reformulation with `j ≤ p - 2` when `d ^ p = 0`: all `SlashHomology p d j` for `j ≤ p - 2`
vanish iff `ker(d ^ m) = im(d ^ (p - m))` for every `m ≤ p`. -/
theorem forall_le_sub_two_subsingleton_iff_ker_pow_eq_range_pow {p : ℕ} {d : M →ₗ[R] M}
    (hd : d ^ p = 0) :
    (∀ j ≤ p - 2, Subsingleton (SlashHomology p d j)) ↔
      ∀ m ≤ p, LinearMap.ker (d ^ m) = LinearMap.range (d ^ (p - m)) := by
  rw [← forall_subsingleton_iff_ker_pow_eq_range_pow hd]
  match p with
  | 0 =>
    have := subsingleton_of_pow_zero_eq_zero hd
    exact ⟨fun _ j hj ↦ (Nat.not_lt_zero _ hj).elim, fun _ _ _ ↦ inferInstance⟩
  | 1 =>
    refine ⟨fun _ j hj ↦ (by omega), fun _ j hj ↦ ?_⟩
    obtain rfl : j = 0 := by omega
    rw [subsingleton_iff]; simp [Module.End.one_eq_id]
  | p + 2 =>
    exact ⟨fun h j hj ↦ h j (by omega), fun h j hj ↦ h j (by omega)⟩

end SlashHomology

end Ring

/-! ### Monomial bases and Khovanov–Qi's dimension decomposition over a division ring -/

namespace SlashHomology

section DivisionRing

universe v

variable {k : Type*} {M : Type v} [DivisionRing k] [AddCommGroup M] [Module k M]

/-- **Monomial `k`-basis from vanishing slash homology.** Over a division ring `k` (without
assuming finite dimensionality), if `d : M →ₗ[k] M` satisfies `d ^ p = 0` and all
`SlashHomology p d j` for `j + 1 < p` vanish, then there exist an index type `ι`, a family
`v : ι → M`, and a `k`-basis `b : Module.Basis (ι × Fin p) k M` with `b (i, r) = (d ^ r) (v i)`. -/
theorem exists_basis_pow_of_forall_subsingleton {p : ℕ} {d : M →ₗ[k] M} (hd : d ^ p = 0)
    (hsub : ∀ j, j + 1 < p → Subsingleton (SlashHomology p d j)) :
    ∃ (ι : Type v) (v : ι → M) (b : Module.Basis (ι × Fin p) k M),
      ∀ (i : ι) (r : Fin p), b (i, r) = (d ^ (r : ℕ)) (v i) := by
  obtain ⟨W, hW⟩ := (LinearMap.range d).exists_isCompl
  obtain ⟨ι, ⟨bW⟩⟩ : ∃ (ι : Type v), Nonempty (Module.Basis ι k W) :=
    ⟨Module.Basis.ofVectorSpaceIndex k W, ⟨Module.Basis.ofVectorSpace k W⟩⟩
  have hker : LinearMap.ker (d ^ (p - 1)) ≤ LinearMap.range d := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · have := subsingleton_of_pow_zero_eq_zero hd
      exact fun x _ ↦ Subsingleton.elim x 0 ▸ zero_mem _
    · have h1 := (forall_subsingleton_iff_ker_pow_eq_range_pow hd).mp hsub (p - 1) (by omega)
      rw [show p - (p - 1) = 1 by omega, pow_one] at h1
      exact h1.le
  have hli :=
    Module.End.linearIndependent_pow_of_disjoint d hW.disjoint hd hker bW.linearIndependent
  have hspan : (⊤ : Submodule k M) ≤
      Submodule.span k (Set.range fun ir : ι × Fin p ↦ (d ^ (ir.2 : ℕ)) (bW ir.1 : M)) := by
    refine (Module.End.iSup_map_pow_eq_top_of_codisjoint d hW.codisjoint hd).ge.trans
      (iSup_le fun r ↦ ?_)
    rintro _ ⟨w, hw, rfl⟩
    have happ := congrArg (fun x : W ↦ (d ^ (r : ℕ)) (x : M)) (bW.linearCombination_repr ⟨w, hw⟩)
    dsimp only at happ
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, _root_.map_sum] at happ
    rw [← happ]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [Submodule.coe_smul_of_tower, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, r), rfl⟩)
  exact ⟨ι, fun i ↦ (bW i : M), Module.Basis.mk hli hspan, fun _ _ ↦ by simp⟩

/-- For a finite-dimensional `p`-complex (`d ^ p = 0`) and `j < p`,
`dim H^{/j}(M) + dim ker(d ^ j) + dim im(d ^ (p - 1)) = dim ker(d ^ (j + 1))`. -/
theorem finrank_add_finrank_ker_add_finrank_range [FiniteDimensional k M]
    {p : ℕ} {d : M →ₗ[k] M} (hd : d ^ p = 0) {j : ℕ} (hj : j < p) :
    Module.finrank k (SlashHomology p d j) + Module.finrank k (LinearMap.ker (d ^ j)) +
        Module.finrank k (LinearMap.range (d ^ (p - 1))) =
      Module.finrank k (LinearMap.ker (d ^ (j + 1))) := by
  let S := LinearMap.range (d ^ (p - j - 1))
  let K := LinearMap.ker (d ^ j)
  have hbd : Module.finrank k (boundaries p d j) = Module.finrank k ↥(S ⊔ K) :=
    (Submodule.comapSubtypeEquivOfLe (range_sup_ker_le_ker hd j)).finrank_eq
  let f : S →ₗ[k] M := (d ^ j).domRestrict S
  have hfrange : LinearMap.range f = LinearMap.range (d ^ (p - 1)) := by
    rw [LinearMap.range_domRestrict, ← LinearMap.range_comp, ← Module.End.mul_eq_comp, ← pow_add,
      show j + (p - j - 1) = p - 1 by omega]
  have hfker : Module.finrank k (LinearMap.ker f) = Module.finrank k ↥(S ⊓ K) := by
    rw [← Submodule.finrank_map_subtype_eq S, LinearMap.ker_domRestrict,
      Submodule.map_comap_subtype]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hfrange, hfker] at hrn
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq S K
  have hquot : Module.finrank k (SlashHomology p d j) + Module.finrank k (boundaries p d j) =
      Module.finrank k (LinearMap.ker (d ^ (j + 1))) :=
    (boundaries p d j).finrank_quotient_add_finrank
  rw [hbd] at hquot
  dsimp only [S, K] at hrn hmod hquot
  omega

/-- **Khovanov–Qi's dimension decomposition** (arXiv:1208.0616, §2, equation (20)). For any
finite-dimensional vector space `M` over a division ring `k` and endomorphism `d : M →ₗ[k] M` with
`d ^ p = 0`,
`finrank k M = p * finrank k (range (d ^ (p - 1))) + ∑_{j = 0}^{p - 2} finrank k H^{/j}(M)`. -/
theorem finrank_eq_mul_finrank_range_pow_add_sum [FiniteDimensional k M]
    {p : ℕ} {d : M →ₗ[k] M} (hd : d ^ p = 0) :
    Module.finrank k M =
      p * Module.finrank k (LinearMap.range (d ^ (p - 1))) +
        ∑ j ∈ Finset.range (p - 1), Module.finrank k (SlashHomology p d j) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have := subsingleton_of_pow_zero_eq_zero hd
    simp [Module.finrank_zero_of_subsingleton]
  have htel : ∀ m ≤ p - 1,
      Module.finrank k (LinearMap.ker (d ^ m)) =
        m * Module.finrank k (LinearMap.range (d ^ (p - 1))) +
          ∑ j ∈ Finset.range m, Module.finrank k (SlashHomology p d j) := by
    intro m hm
    induction m with
    | zero => simp [Module.End.one_eq_id]
    | succ m ih =>
      rw [Finset.sum_range_succ, ← finrank_add_finrank_ker_add_finrank_range hd (by omega),
        ih (by omega), Nat.succ_mul]
      omega
  have hp1 := htel (p - 1) le_rfl
  have hrn := LinearMap.finrank_range_add_finrank_ker (d ^ (p - 1))
  have hmul :
      Module.finrank k (LinearMap.range (d ^ (p - 1))) +
          (p - 1) * Module.finrank k (LinearMap.range (d ^ (p - 1))) =
        p * Module.finrank k (LinearMap.range (d ^ (p - 1))) := by
    simpa [one_mul, add_comm] using
      (Nat.add_mul 1 (p - 1) (Module.finrank k (LinearMap.range (d ^ (p - 1))))).symm.trans
        (by rw [show 1 + (p - 1) = p by omega])
  omega

end DivisionRing

end SlashHomology

end TauCeti
