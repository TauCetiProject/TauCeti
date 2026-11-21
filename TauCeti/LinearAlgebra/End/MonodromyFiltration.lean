/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.End.JordanChain.Basic
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
`F (c + r) ⊓ (N ^ r)⁻¹ (F (c - r - 1)) = F (c + r - 1)` says that it is injective.

## Main definitions and results

* `Module.End.monodromyFiltration N a`: the kernel-image formula.
* `Module.End.IsMonodromyFiltration N c F`: `F` is a finite increasing filtration, lowered by
  two steps by `N`, for which the powers of `N` induce isomorphisms between the graded pieces
  placed symmetrically about the centre `c`.
* `Module.End.IsMonodromyFiltration.unique`: over any semiring, such a filtration is unique.
* `Module.End.map_pow_monodromyFiltration_sup`: the powers of `N` are surjective on the graded
  pieces of the kernel-image filtration, for any endomorphism of any module.
* `Module.End.JordanChainBasis.monodromyFiltration_eq_span`: in a Jordan-chain basis, the
  filtration is spanned by the chain vectors `N ^ j (head i)` of weight `len i - 1 - 2 j ≤ a`.
* `Module.End.isMonodromyFiltration_iff`: for a nilpotent endomorphism of a finite-dimensional
  vector space, the monodromy filtrations centred at `c` are exactly the shifted kernel-image
  filtration `a ↦ monodromyFiltration N (a - c)`.
* `Module.End.monodromyFiltration_conj`, `Module.End.monodromyFiltration_smul` and
  `Module.End.map_monodromyFiltration_of_conj_eq_smul`: transport under conjugation, invariance
  under nonzero scalars, and stability under automorphisms that rescale `N`, such as Frobenius
  with `N F = q F N`.

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

/-- The endomorphism `N` lowers the monodromy filtration by two steps. -/
theorem map_monodromyFiltration_le (a : ℤ) :
    (N.monodromyFiltration a).map N ≤ N.monodromyFiltration (a - 2) := by
  rw [map_le_iff_le_comap, monodromyFiltration_le_iff]
  rintro i j rfl x ⟨hx, y, rfl⟩
  rw [mem_comap]
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hx
  cases i with
  | zero => simp_all
  | succ i =>
    refine N.ker_pow_inf_range_pow_le_monodromyFiltration_of_eq (i := i) (j := j + 1)
      (by push_cast; ring) ⟨?_, y, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, ← _root_.mul_apply_eq_comp, ← pow_succ, hx]
    · rw [pow_succ', _root_.mul_apply_eq_comp]

/-- The power `N ^ k` lowers the monodromy filtration by `2 k` steps. -/
theorem map_pow_monodromyFiltration_le (k : ℕ) (a : ℤ) :
    (N.monodromyFiltration a).map (N ^ k) ≤ N.monodromyFiltration (a - 2 * k) := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_eq_comp, map_comp]
    refine (map_mono ih).trans ((N.map_monodromyFiltration_le _).trans_eq ?_)
    congr 1
    push_cast
    ring

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
  rintro i j hij x ⟨hx, y, rfl⟩
  obtain rfl : j = i + r := by omega
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hx
  refine ⟨(N ^ i) y, N.ker_pow_inf_range_pow_le_monodromyFiltration_of_eq (i := i + r) (j := i)
    (by push_cast; ring) ⟨?_, y, rfl⟩, ?_⟩
  · rw [SetLike.mem_coe, LinearMap.mem_ker, ← _root_.mul_apply_eq_comp, ← pow_add]
    rw [← _root_.mul_apply_eq_comp, ← pow_add] at hx
    rwa [show i + r + 1 + i = i + 1 + (i + r) by ring]
  · rw [← _root_.mul_apply_eq_comp, ← pow_add, add_comm]

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

end IsMonodromyFiltration

/-- The step `r - 1` of the monodromy filtration consists of vectors of the step `r` sent by
`N ^ r` into the step `-r - 1`. This is the inclusion that holds for every endomorphism; the
reverse inclusion, injectivity of `gr_r → gr_{-r}`, is
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

end FiniteDimensional

end Module.End
