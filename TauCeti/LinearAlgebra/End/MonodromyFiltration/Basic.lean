/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.End.JordanChain.Basic
public import TauCeti.Algebra.Module.Filtration.Basic
import TauCeti.Algebra.Module.Equiv.Basic

/-!
# The monodromy filtration of a nilpotent endomorphism

For an endomorphism `N` of a module `V`, the *monodromy filtration* is the increasing
`ℤ`-indexed filtration given by the kernel-image formula
`M a = ∑_{i - j = a} ker N ^ (i + 1) ⊓ range N ^ j` (`i, j ≥ 0`). When `N` is a nilpotent
endomorphism of a finite-dimensional vector space it is the unique finite increasing filtration
with `N (M a) ⊆ M (a - 2)` for which each power `N ^ r` induces an isomorphism
`gr_r ≅ gr_{-r}` of graded pieces. On a Jordan block of length `d + 1` the chain vectors
`v, N v, …, N ^ d v` have weights `d, d - 2, …, -d`, so the filtration is centred at `0` and
differs from the kernel filtration `ker N ^ j`.

The monodromy filtration is the linear algebra behind the local monodromy of a degenerating
family: for a quasi-unipotent `ℓ`-adic representation of inertia, the logarithm `N` of the
unipotent part is nilpotent and its monodromy filtration organises the cohomology of the
generic fibre, as in the weight-monodromy conjecture and the Picard–Lefschetz formula.

The two isomorphism conditions are expressed by subobject equalities, without forming
quotients: for each `r ≥ 0`, `N ^ r (F (c + r)) ⊔ F (c - r - 1) = F (c - r)` says that the map
`gr_{c + r} → gr_{c - r}` induced by `N ^ r` is surjective, and
`F (c + r) ⊓ (N ^ r)⁻¹ (F (c - r - 1)) = F (c + r - 1)` says that it is injective. The graded
pieces themselves, `TauCeti.GradedPiece F a`, appear for the induced maps and primitive parts.

## Main definitions and results

* `Module.End.monodromyFiltration N a`: the kernel-image formula.
* `Module.End.IsMonodromyFiltration N c F`: `F` is a finite increasing filtration, lowered by
  two steps by `N`, for which the powers of `N` induce isomorphisms between the graded pieces
  placed symmetrically about the centre `c`.
* `Module.End.IsMonodromyFiltration.unique`: over any semiring, such a filtration is unique.
* `Module.End.IsMonodromyFiltration.isNilpotent`: an endomorphism with a monodromy filtration is
  nilpotent.
* `Module.End.map_pow_monodromyFiltration_sup`: the powers of `N` are surjective on the graded
  pieces of the kernel-image filtration, for any endomorphism of any module.
* `Module.End.JordanChainBasis.monodromyFiltration_eq_span`: in a Jordan-chain basis, the
  filtration is spanned by the chain vectors `N ^ j (head i)` of weight `len i - 1 - 2 j ≤ a`.
* `Module.End.isMonodromyFiltration_iff`: for a nilpotent endomorphism of a finite-dimensional
  vector space, the monodromy filtrations centred at `c` are exactly the shifted kernel-image
  filtration `a ↦ monodromyFiltration N (a - c)`.
* `Module.End.IsMonodromyFiltration.isStrict`: over any ring, `N` is strict for a monodromy
  filtration, `N (F (a + 2)) = range N ⊓ F a`; `Module.End.isStrict_monodromyFiltration` is the
  case of the kernel-image filtration of a nilpotent endomorphism of a finite-dimensional space.
* `Module.End.gradedPieceMap` and `Module.End.primitivePart`: the map `gr_a → gr_{a - 2}` induced
  by `N` and its kernel `P_a`, the primitive part in the lower convention.
* `Module.End.IsMonodromyFiltration.gradedPiece_mapOfLE_pow_bijective`: `N ^ r` induces a
  bijection `gr_{c + r} → gr_{c - r}`.
* `Module.End.IsMonodromyFiltration.primitivePart_eq_bot_of_lt` and
  `Module.End.IsMonodromyFiltration.gradedPieceKerEquiv`: `P_a = 0` for `a > c`, and
  `gr_a (ker N) ≅ P_a` for the filtration induced on `ker N`, a consequence of strictness.
* `Module.End.monodromyFiltration_conj`, `Module.End.monodromyFiltration_smul` and
  `Module.End.map_monodromyFiltration_of_conj_eq_smul`: transport under conjugation, invariance
  under nonzero scalars, and stability under automorphisms that rescale `N`, such as Frobenius
  with `N F = q F N`.

## Implementation notes

Strictness is proved from the defining conditions alone, so it holds for modules over any ring,
without a Jordan decomposition. By `LinearMap.isStrict_iff_forall_map_add_one_inf_le` it suffices
to move `y ∈ F (a + 3)` with `N y ∈ F a` down to `F (a + 2)` without changing `N y`. Above the
centre, injectivity of `N` on graded pieces does this directly. At or below the centre, `y` is
congruent to `N ^ k z` with `z` in the opposite step, and graded surjectivity in ever lower steps
corrects `z` until `N ^ (k + 1)` kills it.

## References

* P. Deligne, *La conjecture de Weil. II*, Publ. Math. IHÉS **52** (1980), §1.6, 1.6.1–1.6.14.
* L. Illusie, *Autour du théorème de monodromie locale*, Astérisque **223** (1994), §1.
-/

public section

open Submodule

namespace Module.End

variable {R K V W : Type*}

section Semiring

variable [Semiring R] [AddCommMonoid V] [Module R V] (N : Module.End R V)

/-- The monodromy filtration of an endomorphism `N`, centred at `0`, given by the kernel-image
formula `M a = ∑_{i - j = a} ker N ^ (i + 1) ⊓ range N ^ j` over natural numbers `i, j`. For a
nilpotent endomorphism of a finite-dimensional vector space it is characterized by
`Module.End.isMonodromyFiltration_iff`. -/
noncomputable def monodromyFiltration (a : ℤ) : Submodule R V :=
  ⨆ (i : ℕ) (j : ℕ) (_ : (i : ℤ) - j = a),
    LinearMap.ker (N ^ (i + 1)) ⊓ LinearMap.range (N ^ j)

/-- The kernel-image formula defining the monodromy filtration. -/
theorem monodromyFiltration_def (a : ℤ) :
    N.monodromyFiltration a = ⨆ (i : ℕ) (j : ℕ) (_ : (i : ℤ) - j = a),
      LinearMap.ker (N ^ (i + 1)) ⊓ LinearMap.range (N ^ j) := by
  rw [monodromyFiltration]

/-- The monodromy filtration is the smallest submodule containing each
`ker N ^ (i + 1) ⊓ range N ^ j` with `i - j = a`. -/
theorem monodromyFiltration_le_iff {a : ℤ} {p : Submodule R V} :
    N.monodromyFiltration a ≤ p ↔ ∀ i j : ℕ, (i : ℤ) - j = a →
      LinearMap.ker (N ^ (i + 1)) ⊓ LinearMap.range (N ^ j) ≤ p := by
  simp only [monodromyFiltration, iSup_le_iff]

/-- Each term `ker N ^ (i + 1) ⊓ range N ^ j` lies in the step `i - j` of the monodromy
filtration. -/
theorem ker_pow_inf_range_pow_le_monodromyFiltration_of_eq {i j : ℕ} {a : ℤ}
    (h : (i : ℤ) - j = a) :
    LinearMap.ker (N ^ (i + 1)) ⊓ LinearMap.range (N ^ j) ≤ N.monodromyFiltration a :=
  (N.monodromyFiltration_le_iff.1 le_rfl) i j h

/-- The monodromy filtration is increasing. -/
theorem monodromyFiltration_mono : Monotone N.monodromyFiltration := by
  refine monotone_int_of_le_succ fun a => ?_
  rw [monodromyFiltration_le_iff]
  rintro i j rfl
  refine le_trans ?_ (N.ker_pow_inf_range_pow_le_monodromyFiltration_of_eq
    (i := i + 1) (j := j) (by push_cast; ring))
  refine inf_le_inf_right _ fun x hx => ?_
  rw [LinearMap.mem_ker] at hx ⊢
  rw [pow_succ', _root_.mul_apply_eq_comp, hx, map_zero]

/-- The term `ker N ^ (i + 1) ⊓ range N ^ j` lies in every step `a ≥ i - j` of the monodromy
filtration. -/
theorem ker_pow_inf_range_pow_le_monodromyFiltration {i j : ℕ} {a : ℤ}
    (h : (i : ℤ) - j ≤ a) :
    LinearMap.ker (N ^ (i + 1)) ⊓ LinearMap.range (N ^ j) ≤ N.monodromyFiltration a :=
  (N.ker_pow_inf_range_pow_le_monodromyFiltration_of_eq rfl).trans
    (N.monodromyFiltration_mono h)

/-- The kernel of `N ^ k` lies in the step `k - 1` of the monodromy filtration. -/
theorem ker_pow_le_monodromyFiltration (k : ℕ) :
    LinearMap.ker (N ^ k) ≤ N.monodromyFiltration (k - 1) := by
  cases k with
  | zero => simp [Module.End.one_eq_id]
  | succ k =>
    refine le_trans ?_ (N.ker_pow_inf_range_pow_le_monodromyFiltration (i := k) (j := 0)
      (by omega))
    simp [Module.End.one_eq_id]

/-- The power `N ^ k` maps `ker N ^ (i + k + 1) ⊓ range N ^ j` onto
`ker N ^ (i + 1) ⊓ range N ^ (j + k)`. -/
theorem map_pow_ker_pow_inf_range_pow (i k j : ℕ) :
    (LinearMap.ker (N ^ (i + k + 1)) ⊓ LinearMap.range (N ^ j)).map (N ^ k) =
      LinearMap.ker (N ^ (i + 1)) ⊓ LinearMap.range (N ^ (j + k)) := by
  ext z
  simp only [mem_map, mem_inf, LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨hx, y, rfl⟩, rfl⟩
    refine ⟨?_, y, ?_⟩
    · rwa [← _root_.mul_apply_eq_comp, ← pow_add, add_right_comm]
    · rw [← _root_.mul_apply_eq_comp, ← pow_add, add_comm]
  · rintro ⟨hz, y, rfl⟩
    refine ⟨(N ^ j) y, ⟨?_, y, rfl⟩, ?_⟩
    · rw [← _root_.mul_apply_eq_comp, ← pow_add] at hz ⊢
      rwa [show i + k + 1 + j = i + 1 + (j + k) by ring]
    · rw [← _root_.mul_apply_eq_comp, ← pow_add, add_comm]

/-- If `N` lowers a `ℤ`-indexed family of submodules by two steps, the power `N ^ k` lowers it by
`2 k` steps. -/
theorem map_pow_le_of_map_le {N : Module.End R V} {F : ℤ → Submodule R V}
    (h : ∀ a, (F a).map N ≤ F (a - 2)) (k : ℕ) (a : ℤ) : (F a).map (N ^ k) ≤ F (a - 2 * k) := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_eq_comp, map_comp]
    exact (map_mono ih).trans ((h _).trans_eq (by congr 1; push_cast; ring))

/-- The endomorphism `N` lowers the monodromy filtration by two steps. -/
theorem map_monodromyFiltration_le (a : ℤ) :
    (N.monodromyFiltration a).map N ≤ N.monodromyFiltration (a - 2) := by
  rw [map_le_iff_le_comap, monodromyFiltration_le_iff]
  rintro i j rfl
  cases i with
  | zero => exact inf_le_left.trans (by simp)
  | succ i =>
    rw [← map_le_iff_le_comap]
    have h := N.map_pow_ker_pow_inf_range_pow i 1 j
    rw [pow_one] at h
    rw [h]
    exact N.ker_pow_inf_range_pow_le_monodromyFiltration_of_eq (by push_cast; ring)

/-- The power `N ^ k` lowers the monodromy filtration by `2 k` steps. -/
theorem map_pow_monodromyFiltration_le (k : ℕ) (a : ℤ) :
    (N.monodromyFiltration a).map (N ^ k) ≤ N.monodromyFiltration (a - 2 * k) :=
  map_pow_le_of_map_le N.map_monodromyFiltration_le k a

/-- If `N ^ (d + 1) = 0`, the monodromy filtration vanishes at and below `-d - 1`. -/
theorem monodromyFiltration_eq_bot_of_le {d : ℕ} (hd : N ^ (d + 1) = 0) {a : ℤ}
    (ha : a ≤ -d - 1) : N.monodromyFiltration a = ⊥ := by
  rw [eq_bot_iff, monodromyFiltration_le_iff]
  rintro i j rfl
  rw [pow_eq_zero_of_le (n := j) (by omega) hd, LinearMap.range_zero]
  exact inf_le_right

/-- If `N ^ (d + 1) = 0`, the monodromy filtration is everything at and above `d`. -/
theorem monodromyFiltration_eq_top_of_le {d : ℕ} (hd : N ^ (d + 1) = 0) {a : ℤ}
    (ha : d ≤ a) : N.monodromyFiltration a = ⊤ := by
  refine eq_top_iff.2 (le_trans ?_ (N.ker_pow_inf_range_pow_le_monodromyFiltration
    (i := d) (j := 0) (by simpa using ha)))
  simp [hd, Module.End.one_eq_id]

/-- The monodromy filtration of the zero endomorphism vanishes in negative degrees. -/
theorem monodromyFiltration_zero_eq_bot_of_neg {a : ℤ} (ha : a < 0) :
    (0 : Module.End R V).monodromyFiltration a = ⊥ :=
  monodromyFiltration_eq_bot_of_le _ (d := 0) (by simp) (by omega)

/-- The monodromy filtration of the zero endomorphism is everything in nonnegative degrees. -/
theorem monodromyFiltration_zero_eq_top_of_nonneg {a : ℤ} (ha : 0 ≤ a) :
    (0 : Module.End R V).monodromyFiltration a = ⊤ :=
  monodromyFiltration_eq_top_of_le _ (d := 0) (by simp) (by omega)

/-- The power `N ^ r` maps the step `r` of the monodromy filtration onto the step `-r` modulo the
step `-r - 1`: the map `gr_r → gr_{-r}` induced by `N ^ r` is surjective. This holds for every
endomorphism of every module. -/
theorem map_pow_monodromyFiltration_sup (r : ℕ) :
    (N.monodromyFiltration r).map (N ^ r) ⊔ N.monodromyFiltration (-r - 1) =
      N.monodromyFiltration (-r) := by
  refine le_antisymm (sup_le ((N.map_pow_monodromyFiltration_le r r).trans_eq ?_)
    (N.monodromyFiltration_mono (by omega))) (le_sup_of_le_left ?_)
  · congr 1
    ring
  rw [monodromyFiltration_le_iff]
  rintro i j hij
  obtain rfl : j = i + r := by omega
  rw [← N.map_pow_ker_pow_inf_range_pow]
  exact map_mono (N.ker_pow_inf_range_pow_le_monodromyFiltration_of_eq (by push_cast; ring))

/-- `F` is a monodromy filtration of `N` centred at `c`: a finite increasing filtration, lowered
by two steps by `N`, such that for every `r ≥ 0` the map `gr_{c + r} → gr_{c - r}` induced by
`N ^ r` is an isomorphism. Surjectivity is the equality `map_pow_sup` and injectivity the equality
`inf_comap_pow`. -/
structure IsMonodromyFiltration (c : ℤ) (F : ℤ → Submodule R V) : Prop where
  /-- The filtration is increasing. -/
  monotone : Monotone F
  /-- The filtration vanishes from some step down. -/
  exists_eq_bot : ∃ a, F a = ⊥
  /-- The filtration is everything from some step up. -/
  exists_eq_top : ∃ b, F b = ⊤
  /-- The endomorphism `N` lowers the filtration by two steps. -/
  map_le (a : ℤ) : (F a).map N ≤ F (a - 2)
  /-- The map `gr_{c + r} → gr_{c - r}` induced by `N ^ r` is surjective. -/
  map_pow_sup (r : ℕ) : (F (c + r)).map (N ^ r) ⊔ F (c - r - 1) = F (c - r)
  /-- The map `gr_{c + r} → gr_{c - r}` induced by `N ^ r` is injective. -/
  inf_comap_pow (r : ℕ) : F (c + r) ⊓ (F (c - r - 1)).comap (N ^ r) = F (c + r - 1)

namespace IsMonodromyFiltration

variable {N} {c : ℤ} {F G : ℤ → Submodule R V}

/-- A monodromy filtration is everything from `c + B` on and vanishes up to `c - B - 1`, for some
natural number `B`. -/
theorem exists_eq_top_and_eq_bot (hF : N.IsMonodromyFiltration c F) :
    ∃ B : ℕ, ∀ a : ℤ, (c + B ≤ a → F a = ⊤) ∧ (a ≤ c - B - 1 → F a = ⊥) := by
  obtain ⟨a₀, ha₀⟩ := hF.exists_eq_bot
  obtain ⟨b₀, hb₀⟩ := hF.exists_eq_top
  refine ⟨(b₀ - c).toNat + (c - a₀).toNat, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · exact eq_top_iff.2 (hb₀ ▸ hF.monotone (by omega))
  · exact eq_bot_iff.2 (ha₀ ▸ hF.monotone (by omega))

/-- The power `N ^ k` lowers a monodromy filtration by `2 k` steps. -/
theorem map_pow_le (hF : N.IsMonodromyFiltration c F) (k : ℕ) (a : ℤ) :
    (F a).map (N ^ k) ≤ F (a - 2 * k) :=
  map_pow_le_of_map_le hF.map_le k a

/-- The power `N ^ k` sends the step `a` of a monodromy filtration into every step `b` with
`a - 2 k ≤ b`. -/
theorem le_comap_pow (hF : N.IsMonodromyFiltration c F) {k : ℕ} {a b : ℤ} (h : a - 2 * k ≤ b) :
    F a ≤ (F b).comap (N ^ k) :=
  map_le_iff_le_comap.1 ((hF.map_pow_le k a).trans (hF.monotone h))

/-- An endomorphism with a monodromy filtration is nilpotent: a power of `N` lowers the step
where the filtration is everything to a step where it vanishes. -/
theorem isNilpotent (hF : N.IsMonodromyFiltration c F) : IsNilpotent N := by
  obtain ⟨a, ha⟩ := hF.exists_eq_bot
  obtain ⟨b, hb⟩ := hF.exists_eq_top
  refine ⟨(b - a).toNat, LinearMap.range_eq_bot.1 (eq_bot_iff.2 ?_)⟩
  rw [← Submodule.map_top, ← hb, ← ha]
  exact (hF.map_pow_le _ b).trans (hF.monotone (by omega))

/-- A monodromy filtration of `N` centred at `c` is unique. -/
theorem unique (hF : N.IsMonodromyFiltration c F) (hG : N.IsMonodromyFiltration c G) :
    F = G := by
  obtain ⟨B₁, hB₁⟩ := hF.exists_eq_top_and_eq_bot
  obtain ⟨B₂, hB₂⟩ := hG.exists_eq_top_and_eq_bot
  set B := max B₁ B₂
  have hB : ∀ a : ℤ, (c + B ≤ a → F a = ⊤ ∧ G a = ⊤) ∧ (a ≤ c - B - 1 → F a = ⊥ ∧ G a = ⊥) :=
    fun a => ⟨fun ha => ⟨(hB₁ a).1 (by omega), (hB₂ a).1 (by omega)⟩,
      fun ha => ⟨(hB₁ a).2 (by omega), (hB₂ a).2 (by omega)⟩⟩
  -- The pairs `(F (c + n), F (c - n - 1))` and `(G (c + n), G (c - n - 1))` agree for `n ≤ B`,
  -- by descending induction on `n`.
  have key : ∀ k n : ℕ, n + k = B → F (c + n) = G (c + n) ∧ F (c - n - 1) = G (c - n - 1) := by
    intro k
    induction k with
    | zero =>
      intro n hn
      exact ⟨((hB _).1 (by omega)).1.trans ((hB _).1 (by omega)).2.symm,
        ((hB _).2 (by omega)).1.trans ((hB _).2 (by omega)).2.symm⟩
    | succ k ih =>
      intro n hn
      obtain ⟨h₁, h₂⟩ := ih (n + 1) (by omega)
      have e₁ : c + n = c + (n + 1 : ℕ) - 1 := by push_cast; ring
      have e₂ : c - n - 1 = c - (n + 1 : ℕ) := by push_cast; ring
      refine ⟨?_, ?_⟩
      · rw [e₁, ← hF.inf_comap_pow, ← hG.inf_comap_pow, h₁, h₂]
      · rw [e₂, ← hF.map_pow_sup, ← hG.map_pow_sup, h₁, h₂]
  funext a
  rcases le_or_gt c a with h | h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = c + n := ⟨(a - c).toNat, by omega⟩
    rcases le_or_gt n B with hn | hn
    · exact (key (B - n) n (by omega)).1
    · exact ((hB _).1 (by omega)).1.trans ((hB _).1 (by omega)).2.symm
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = c - n - 1 := ⟨(c - a - 1).toNat, by omega⟩
    rcases le_or_gt n B with hn | hn
    · exact (key (B - n) n (by omega)).2
    · exact ((hB _).2 (by omega)).1.trans ((hB _).2 (by omega)).2.symm

/-- `N` sends `F a` into `F b` whenever `a - 2 ≤ b`. -/
private theorem apply_mem (hF : N.IsMonodromyFiltration c F) {a b : ℤ} (hb : a - 2 ≤ b) {x : V}
    (hx : x ∈ F a) : N x ∈ F b :=
  hF.monotone hb (hF.map_le a (mem_map_of_mem hx))

/-- `F (a - 1)` lies in `F a` and is sent by `N` into `F (a - 3)`. -/
private theorem le_inf_comap (hF : N.IsMonodromyFiltration c F) (a : ℤ) :
    F (a - 1) ≤ F a ⊓ (F (a - 3)).comap N :=
  le_inf (hF.monotone (by omega)) fun _ hx => hF.apply_mem (by omega) hx

/-- Above the centre of a monodromy filtration, `N` is injective on graded pieces: an element of
`F a`, `c < a`, which `N` sends into `F (a - 3)` already lies in `F (a - 1)`. So the primitive
part `ker (N : gr_a → gr_{a - 2})` vanishes for `a > c`. -/
theorem inf_comap_of_lt (hF : N.IsMonodromyFiltration c F) {a : ℤ} (ha : c < a) :
    F a ⊓ (F (a - 3)).comap N = F (a - 1) := by
  refine le_antisymm ?_ (hF.le_inf_comap a)
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = c + (k + 1 : ℕ) := ⟨(a - c - 1).toNat, by omega⟩
  intro x hx
  obtain ⟨hx, hNx⟩ := mem_inf.1 hx
  -- `N ^ (k + 1) x = N ^ k (N x)` lies in `F (c - k - 2)`, so injectivity of
  -- `N ^ (k + 1) : gr_{c + k + 1} → gr_{c - k - 1}` applies.
  rw [← hF.inf_comap_pow]
  refine mem_inf.2 ⟨hx, ?_⟩
  rw [mem_comap, pow_succ, _root_.mul_apply_eq_comp]
  exact hF.le_comap_pow (k := k) (by omega) hNx

end IsMonodromyFiltration

/-- The step `r - 1` of the monodromy filtration is contained in the set of vectors of the step
`r` sent by `N ^ r` into the step `-r - 1`. This is the inclusion that holds for every
endomorphism; the reverse inclusion, injectivity of `gr_r → gr_{-r}`, is
`Module.End.JordanChainBasis.monodromyFiltration_inf_comap_pow`. -/
theorem monodromyFiltration_le_inf_comap_pow (r : ℕ) :
    N.monodromyFiltration (r - 1) ≤
      N.monodromyFiltration r ⊓ (N.monodromyFiltration (-r - 1)).comap (N ^ r) :=
  le_inf (N.monodromyFiltration_mono (by omega)) (map_le_iff_le_comap.1
    ((N.map_pow_monodromyFiltration_le r _).trans_eq (by congr 1; ring)))

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  (N : Module.End R V)

/-- Conjugation by a linear equivalence transports the monodromy filtration. -/
@[simp]
theorem monodromyFiltration_conj (e : V ≃ₗ[R] W) (a : ℤ) :
    (e.conj N).monodromyFiltration a = (N.monodromyFiltration a).map (e : V →ₗ[R] W) := by
  simp only [monodromyFiltration_def, Submodule.map_iSup, Submodule.map_inf _ e.injective,
    ← LinearEquiv.conj_pow, LinearEquiv.ker_conj, LinearEquiv.range_conj]

end CommSemiring

section Semifield

variable [Semifield K] [AddCommMonoid V] [Module K V] (N : Module.End K V)

/-- The monodromy filtration is unchanged when `N` is multiplied by a nonzero scalar. -/
@[simp]
theorem monodromyFiltration_smul {c : K} (hc : c ≠ 0) :
    (c • N).monodromyFiltration = N.monodromyFiltration := by
  funext a
  simp only [monodromyFiltration_def, smul_pow, LinearMap.ker_smul _ _ (pow_ne_zero _ hc),
    LinearMap.range_smul _ _ (pow_ne_zero _ hc)]

/-- An automorphism `e` rescaling `N` by a nonzero scalar, `e N e⁻¹ = c N`, preserves each step
of the monodromy filtration. For instance a Frobenius `F` with `N F = q F N` preserves it. -/
theorem map_monodromyFiltration_of_conj_eq_smul (e : V ≃ₗ[K] V) {c : K} (hc : c ≠ 0)
    (h : e.conj N = c • N) (a : ℤ) :
    (N.monodromyFiltration a).map (e : V →ₗ[K] V) = N.monodromyFiltration a := by
  rw [← monodromyFiltration_conj, h, monodromyFiltration_smul N hc]

end Semifield

namespace JordanChainBasis

section Semiring

variable [Semiring K] [AddCommMonoid V] [Module K V] {N : Module.End K V} {ι : Type*}

/-- In a Jordan-chain basis, the monodromy filtration is spanned by the chain vectors
`N ^ j (head i)` whose weight `len i - 1 - 2 j` is at most `a`. So a chain of length `d + 1`
contributes one vector in each weight `d, d - 2, …, -d`. -/
theorem monodromyFiltration_eq_span (c : N.JordanChainBasis ι) (a : ℤ) :
    N.monodromyFiltration a =
      span K (c.basis '' {p | (c.len p.1 : ℤ) - 1 - 2 * (p.2 : ℕ) ≤ a}) := by
  refine le_antisymm ?_ (span_le.2 ?_)
  · rw [monodromyFiltration_le_iff]
    rintro i j rfl x ⟨hx, y, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hx
    rw [Basis.mem_span_image]
    rintro ⟨k, l⟩ hp
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hp
    -- A coordinate of a vector of `range N ^ j` has depth at least `j`.
    have hl : j ≤ (l : ℕ) := by
      by_contra! hl
      have := LinearMap.congr_fun (c.basis_coord_comp_pow_eq_zero (p := ⟨k, l⟩) hl) y
      rw [LinearMap.comp_apply, Basis.coord_apply] at this
      exact hp this
    -- A coordinate of a vector killed by `N ^ (i + 1)` has depth at least `len k - i - 1`.
    have hlen : c.len k ≤ l + (i + 1) := by
      by_contra! hlen
      have := c.basis_repr_pow_apply (i + 1) ((N ^ j) y) k l hlen
      rw [hx, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
      exact hp this.symm
    simp only [Set.mem_ofPred_eq]
    omega
  · rintro _ ⟨⟨i, j⟩, hp, rfl⟩
    simp only [Set.mem_ofPred_eq] at hp
    refine N.ker_pow_inf_range_pow_le_monodromyFiltration (i := c.len i - 1 - j) (j := j)
      (by omega) ⟨?_, c.head i, (c.basis_apply ⟨i, j⟩).symm⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, c.basis_apply, ← _root_.mul_apply_eq_comp, ← pow_add]
    exact pow_map_zero_of_le (by dsimp only; omega) (c.pow_len_apply_head i)

/-- In the presence of a Jordan-chain basis, the power `N ^ r` induces an injective map
`gr_r → gr_{-r}` on the graded pieces of the monodromy filtration. -/
theorem monodromyFiltration_inf_comap_pow (c : N.JordanChainBasis ι) (r : ℕ) :
    N.monodromyFiltration r ⊓ (N.monodromyFiltration (-r - 1)).comap (N ^ r) =
      N.monodromyFiltration (r - 1) := by
  refine le_antisymm ?_ (N.monodromyFiltration_le_inf_comap_pow r)
  rintro x ⟨hx, hNx⟩
  rw [SetLike.mem_coe, c.monodromyFiltration_eq_span, Basis.mem_span_image] at hx
  rw [SetLike.mem_coe, mem_comap, c.monodromyFiltration_eq_span, Basis.mem_span_image] at hNx
  rw [c.monodromyFiltration_eq_span, Basis.mem_span_image]
  rintro ⟨k, l⟩ hp
  have hw := hx hp
  simp only [Set.mem_ofPred_eq] at hw ⊢
  by_contra! hw'
  -- The coordinate of `x` at a chain vector of weight exactly `r` reappears in `N ^ r x` at
  -- weight `-r`, which is not allowed.
  have hlt : (l : ℕ) + r < c.len k := by omega
  have := hNx (a := ⟨k, ⟨l + r, hlt⟩⟩) (by
    rw [Finset.mem_coe, Finsupp.mem_support_iff, c.basis_repr_pow_apply]
    exact Finsupp.mem_support_iff.1 hp)
  simp only [Set.mem_ofPred_eq] at this
  omega

end Semiring

end JordanChainBasis

section Ring

open TauCeti

variable [Ring R] [AddCommGroup V] [Module R V] (N : Module.End R V) {F : ℤ → Submodule R V}

/-- The map `gr_a → gr_{a - 2}` induced on the graded pieces of a filtration `F` by an
endomorphism `N` lowering `F` by two steps. -/
noncomputable def gradedPieceMap (hF : ∀ a, (F a).map N ≤ F (a - 2)) (a : ℤ) :
    GradedPiece F a →ₗ[R] GradedPiece F (a - 2) :=
  GradedPiece.mapOfLE N (map_le_iff_le_comap.1 (hF a))
    (map_le_iff_le_comap.1 ((hF (a - 1)).trans_eq (by rw [sub_right_comm])))

section gradedPieceMap

variable {N} (hF : ∀ a, (F a).map N ≤ F (a - 2))

/-- The induced map on graded pieces sends the class of `x` to the class of `N x`. -/
@[simp]
theorem gradedPieceMap_mk {a : ℤ} (x : F a) :
    N.gradedPieceMap hF a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨N x, map_le_iff_le_comap.1 (hF a) x.property⟩ := by
  unfold gradedPieceMap
  exact GradedPiece.mapOfLE_mk _ _ _ x

variable (N) in
/-- The primitive part `P_a = ker (N : gr_a → gr_{a - 2})` of the graded piece `gr_a`, in the lower
convention; Deligne's `P_i = ker (N ^ (i + 1) : gr_i → gr_{-i-2})` is the upper one. For a
monodromy filtration these are the classes at the bottom of the `N`-strings. -/
noncomputable def primitivePart (a : ℤ) : Submodule R (GradedPiece F a) :=
  LinearMap.ker (N.gradedPieceMap hF a)

/-- An element of `gr_a` is primitive exactly when `N` sends it to zero in `gr_{a - 2}`. -/
theorem mem_primitivePart_iff {a : ℤ} {z : GradedPiece F a} :
    z ∈ N.primitivePart hF a ↔ N.gradedPieceMap hF a z = 0 :=
  LinearMap.mem_ker

/-- The class of `x ∈ F a` is primitive exactly when `N x ∈ F (a - 3)`. -/
@[simp]
theorem mk_mem_primitivePart_iff {a : ℤ} (x : F a) :
    Submodule.Quotient.mk x ∈ N.primitivePart hF a ↔ N x ∈ F (a - 3) := by
  rw [mem_primitivePart_iff, gradedPieceMap_mk, GradedPiece.mk_eq_zero_iff,
    show a - 2 - 1 = a - 3 by ring]

end gradedPieceMap

namespace IsMonodromyFiltration

variable {N} {c : ℤ}

/-- Pushing the image `N ^ (k + 1) z` of `z ∈ F (c + k)` down the filtration: if it lies in
`F (c - k - 3 - t)`, then `z` is congruent modulo `F (c + k - 1)` to an element killed by
`N ^ (k + 1)`. -/
private theorem exists_sub_mem_and_pow_apply_eq_zero (hF : N.IsMonodromyFiltration c F) (k : ℕ)
    {z : V} (hz : z ∈ F (c + k)) (t : ℕ) (hNz : (N ^ (k + 1)) z ∈ F (c - k - 3 - t)) :
    ∃ z', z - z' ∈ F (c + k - 1) ∧ (N ^ (k + 1)) z' = 0 := by
  obtain ⟨B, hB⟩ := hF.exists_eq_top_and_eq_bot
  suffices H : ∀ m t : ℕ, B ≤ t + m → ∀ z ∈ F (c + k), (N ^ (k + 1)) z ∈ F (c - k - 3 - t) →
      ∃ z', z - z' ∈ F (c + k - 1) ∧ (N ^ (k + 1)) z' = 0 from H B t (by omega) z hz hNz
  intro m
  induction m with
  | zero =>
    intro t ht z _ hNz
    refine ⟨z, by simp, ?_⟩
    rwa [(hB _).2 (by omega), mem_bot] at hNz
  | succ m ih =>
    intro t ht z hz hNz
    -- Lift `N ^ (k + 1) z` along the surjection `gr_{c + s} → gr_{c - s}`, `s = k + t + 3`.
    have hNz' : (N ^ (k + 1)) z ∈ F (c - (k + t + 3 : ℕ)) := by
      convert hNz using 2
      push_cast
      ring
    rw [← hF.map_pow_sup] at hNz'
    obtain ⟨_, ⟨w, hw, rfl⟩, u, hu, hwu⟩ := mem_sup.1 hNz'
    have hw' : (N ^ (t + 2)) w ∈ F (c + k - 1) := hF.le_comap_pow (k := t + 2) (by omega) hw
    obtain ⟨z', hz', hNz'⟩ := ih (t + 1) (by omega) (z - (N ^ (t + 2)) w)
      (sub_mem hz (hF.monotone (by omega) hw')) (by
        rw [map_sub, ← _root_.mul_apply_eq_comp, ← pow_add,
          show k + 1 + (t + 2) = k + t + 3 by ring, ← hwu, add_sub_cancel_left]
        exact hF.monotone (by omega) hu)
    refine ⟨z', ?_, hNz'⟩
    rw [show z - z' = (N ^ (t + 2)) w + (z - (N ^ (t + 2)) w - z') by abel]
    exact add_mem hw' hz'

/-- **Strictness of `N`** for its monodromy filtration: `N (F (a + 2)) = range N ⊓ F a` for every
`a`. This holds for every module over every ring. -/
theorem isStrict (hF : N.IsMonodromyFiltration c F) : N.IsStrict (fun a => F (a + 2)) F := by
  obtain ⟨B, hB⟩ := hF.exists_eq_top_and_eq_bot
  -- By the one-step criterion, it suffices to lower `y ∈ F (a + 3)` with `N y ∈ F a` to
  -- `F (a + 2)` without changing `N y`.
  refine (LinearMap.isStrict_iff_forall_map_add_one_inf_le (fun _ _ h => hF.monotone (by omega))
    hF.monotone (fun a => map_le_iff_le_comap.1 ((hF.map_le _).trans_eq
      (by rw [add_sub_cancel_right])))
    (eq_top_iff.2 (le_iSup_of_le (c + B - 2) (by rw [sub_add_cancel, (hB _).1 le_rfl])))).2
    fun a => ?_
  rintro _ ⟨⟨y, hy, rfl⟩, hNy⟩
  rw [show a + 1 + 2 = a + 3 by ring] at hy
  rcases lt_or_ge c (a + 3) with hc | hc
  · -- Above the centre, `N` is injective on graded pieces, so `y` lies in `F (a + 2)`.
    refine mem_map_of_mem ?_
    rw [show a + 2 = a + 3 - 1 by ring, ← hF.inf_comap_of_lt hc]
    exact ⟨hy, hF.monotone (by omega) hNy⟩
  -- At or below the centre, write `y = N ^ k z + y₁` with `y₁ ∈ F (a + 2)` and replace `z` by an
  -- element `z'` killed by `N ^ (k + 1)`.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a + 3 = c - k := ⟨(c - a - 3).toNat, by omega⟩
  rw [hk, ← hF.map_pow_sup] at hy
  obtain ⟨_, ⟨z, hz, rfl⟩, y₁, hy₁, rfl⟩ := mem_sup.1 hy
  have hNy₁ : N y₁ ∈ F (c - k - 3) := hF.apply_mem (by omega) hy₁
  obtain ⟨z', hzz', hNz'⟩ := hF.exists_sub_mem_and_pow_apply_eq_zero k hz 0 (by
    rw [show (N ^ (k + 1)) z = N ((N ^ k) z + y₁) - N y₁ by
      rw [map_add, add_sub_cancel_right, pow_succ', _root_.mul_apply_eq_comp]]
    exact sub_mem (hF.monotone (by omega) hNy) (hF.monotone (by omega) hNy₁))
  have key : N ((N ^ k) (z - z') + y₁) = N ((N ^ k) z + y₁) := by
    rw [map_add, map_add, map_sub, map_sub, ← _root_.mul_apply_eq_comp N (N ^ k) z', ← pow_succ',
      hNz', sub_zero]
  rw [← key]
  exact mem_map_of_mem (add_mem (hF.le_comap_pow (k := k) (by omega) hzz')
    (hF.monotone (by omega) hy₁))

/-- The kernel of `N` and a monodromy filtration: an element of `F a` is sent by `N` into
`F (a - 3)` exactly when it is congruent modulo `F (a - 1)` to an element of `ker N ⊓ F a`. This is
the statement `gr_a (ker N) ≅ P_a` of `gradedPieceKerEquiv` without quotients. -/
theorem ker_inf_sup (hF : N.IsMonodromyFiltration c F) (a : ℤ) :
    LinearMap.ker N ⊓ F a ⊔ F (a - 1) = F a ⊓ (F (a - 3)).comap N := by
  refine le_antisymm (sup_le (le_inf inf_le_right fun x hx => ?_) (hF.le_inf_comap a)) ?_
  · rw [mem_comap, LinearMap.mem_ker.1 hx.1]
    exact zero_mem _
  intro y hy
  obtain ⟨hy, hNy⟩ := mem_inf.1 hy
  have h := LinearMap.isStrict_iff.1 hF.isStrict (a - 3)
  rw [show a - 3 + 2 = a - 1 by ring] at h
  obtain ⟨y', hy', hNy'⟩ : N y ∈ (F (a - 1)).map N := h ▸ ⟨⟨y, rfl⟩, hNy⟩
  rw [show y = (y - y') + y' by abel]
  exact add_mem_sup (mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hNy', sub_self]),
    sub_mem hy (hF.monotone (by omega) hy')⟩) hy'

/-- The primitive part `P_a` of a monodromy filtration vanishes above the centre `c`. -/
theorem primitivePart_eq_bot_of_lt (hF : N.IsMonodromyFiltration c F) {a : ℤ} (ha : c < a) :
    N.primitivePart hF.map_le a = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  induction z using Submodule.Quotient.induction_on with | _ x
  rw [mk_mem_primitivePart_iff] at hz
  rw [mem_bot, GradedPiece.mk_eq_zero_iff, ← hF.inf_comap_of_lt ha]
  exact ⟨x.property, hz⟩

/-- For a monodromy filtration centred at `c`, the map `gr_{c + r} → gr_{c - r}` induced by
`N ^ r` is bijective. -/
theorem gradedPiece_mapOfLE_pow_bijective (hF : N.IsMonodromyFiltration c F) (r : ℕ)
    (h : F (c + r) ≤ (F (c - r)).comap (N ^ r))
    (h' : F (c + r - 1) ≤ (F (c - r - 1)).comap (N ^ r)) :
    Function.Bijective (GradedPiece.mapOfLE (N ^ r) h h') := by
  rw [Function.Bijective, GradedPiece.mapOfLE_injective_iff, GradedPiece.mapOfLE_surjective_iff,
    hF.inf_comap_pow, hF.map_pow_sup]
  exact ⟨le_rfl, le_rfl⟩

/-- The map `gr_a (ker N) → gr_a` induced by the inclusion of the filtration `ker N ⊓ F` into
`F` has image the primitive part `P_a`. -/
private theorem range_gradedPiece_mapOfLE_id_eq_primitivePart
    (hF : N.IsMonodromyFiltration c F) (a : ℤ) :
    LinearMap.range (GradedPiece.mapOfLE (F := fun b => LinearMap.ker N ⊓ F b) LinearMap.id
      (p := a) (q := a) (inf_le_right.trans_eq (comap_id _).symm)
      (inf_le_right.trans_eq (comap_id _).symm)) = N.primitivePart hF.map_le a := by
  ext z
  induction z using Submodule.Quotient.induction_on with | _ y
  rw [mk_mem_primitivePart_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    induction w using Submodule.Quotient.induction_on with | _ x
    rw [GradedPiece.mapOfLE_mk, GradedPiece.mk_eq_mk_iff, Subtype.coe_mk, LinearMap.id_apply] at hw
    have hx := mem_comap.1 (mem_inf.1
      ((hF.ker_inf_sup a).le (mem_sup_left x.property))).2
    rw [show (y : V) = x - (x - y) by abel, map_sub]
    exact sub_mem hx (hF.apply_mem (by omega) hw)
  · intro hNy
    obtain ⟨x, hx, w, hw, hxw⟩ :=
      mem_sup.1 ((hF.ker_inf_sup a).ge ⟨y.property, hNy⟩)
    refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
    rw [GradedPiece.mapOfLE_mk, GradedPiece.mk_eq_mk_iff, ← hxw]
    simpa using hw

/-- For a monodromy filtration, the graded pieces of the filtration `ker N ⊓ F` induced on the
kernel of `N` are the primitive parts: `gr_a (ker N) ≅ P_a`, the class of `x ∈ ker N ⊓ F a`
going to its class in `gr_a`. -/
noncomputable def gradedPieceKerEquiv (hF : N.IsMonodromyFiltration c F) (a : ℤ) :
    GradedPiece (fun b => LinearMap.ker N ⊓ F b) a ≃ₗ[R] N.primitivePart hF.map_le a :=
  (LinearEquiv.ofInjective _ ((GradedPiece.mapOfLE_injective_iff _ _ _).2 fun _ hx => by
    rw [comap_id] at hx
    exact mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).1, (mem_inf.1 hx).2⟩)).trans
    (LinearEquiv.ofEq _ _ (hF.range_gradedPiece_mapOfLE_id_eq_primitivePart a))

/-- The isomorphism `gr_a (ker N) ≅ P_a` sends the class of `x` to its class in `gr_a`. -/
@[simp]
theorem coe_gradedPieceKerEquiv_mk (hF : N.IsMonodromyFiltration c F) {a : ℤ}
    (x : ↥(LinearMap.ker N ⊓ F a)) :
    (hF.gradedPieceKerEquiv a (Submodule.Quotient.mk x) : GradedPiece F a) =
      Submodule.Quotient.mk ⟨x, x.property.2⟩ := by
  rw [gradedPieceKerEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply]
  exact GradedPiece.mapOfLE_mk (F := fun b => LinearMap.ker N ⊓ F b) _ _ _ x

end IsMonodromyFiltration

end Ring

section FiniteDimensional

variable [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {N : Module.End K V}

/-- For a nilpotent endomorphism of a finite-dimensional vector space, the power `N ^ r` induces
an injective map `gr_r → gr_{-r}` on the graded pieces of the monodromy filtration. -/
theorem monodromyFiltration_inf_comap_pow (hN : IsNilpotent N) (r : ℕ) :
    N.monodromyFiltration r ⊓ (N.monodromyFiltration (-r - 1)).comap (N ^ r) =
      N.monodromyFiltration (r - 1) := by
  obtain ⟨ι, _, ⟨c⟩⟩ := exists_jordanChainBasis hN
  exact c.monodromyFiltration_inf_comap_pow r

/-- For a nilpotent endomorphism of a finite-dimensional vector space, the kernel-image
filtration shifted to the centre `c` is a monodromy filtration centred at `c`. -/
theorem isMonodromyFiltration_monodromyFiltration (hN : IsNilpotent N) (c : ℤ) :
    N.IsMonodromyFiltration c fun a => N.monodromyFiltration (a - c) := by
  obtain ⟨n, hn⟩ := hN
  have hn' : N ^ (n + 1) = 0 := pow_eq_zero_of_le (Nat.le_succ n) hn
  refine ⟨fun a b hab => N.monodromyFiltration_mono (by omega),
    ⟨c - n - 1, N.monodromyFiltration_eq_bot_of_le hn' (by omega)⟩,
    ⟨c + n, N.monodromyFiltration_eq_top_of_le hn' (by omega)⟩,
    fun a => (N.map_monodromyFiltration_le _).trans_eq (by congr 1; ring),
    fun r => ?_, fun r => ?_⟩
  · rw [show c + (r : ℤ) - c = r by ring, show c - r - 1 - c = -r - 1 by ring,
      show c - r - c = -r by ring]
    exact N.map_pow_monodromyFiltration_sup r
  · rw [show c + (r : ℤ) - c = r by ring, show c - r - 1 - c = -r - 1 by ring,
      show c + r - 1 - c = r - 1 by ring]
    exact monodromyFiltration_inf_comap_pow ⟨n, hn⟩ r

/-- For a nilpotent endomorphism of a finite-dimensional vector space, the monodromy filtration
centred at `c` exists and is unique: it is the kernel-image filtration shifted to `c`. -/
theorem isMonodromyFiltration_iff (hN : IsNilpotent N) {c : ℤ} {F : ℤ → Submodule K V} :
    N.IsMonodromyFiltration c F ↔ F = fun a => N.monodromyFiltration (a - c) :=
  ⟨fun hF => hF.unique (isMonodromyFiltration_monodromyFiltration hN c),
    fun h => h ▸ isMonodromyFiltration_monodromyFiltration hN c⟩

/-- For a nilpotent endomorphism of a finite-dimensional vector space, `N` is strict for its
monodromy filtration: `N (M (a + 2)) = range N ⊓ M a`. -/
theorem isStrict_monodromyFiltration (hN : IsNilpotent N) :
    N.IsStrict (fun a => N.monodromyFiltration (a + 2)) N.monodromyFiltration := by
  simpa using (isMonodromyFiltration_monodromyFiltration hN 0).isStrict

end FiniteDimensional

end Module.End
