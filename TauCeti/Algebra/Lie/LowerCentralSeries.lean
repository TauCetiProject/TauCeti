/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Nilpotent
public import TauCeti.LinearAlgebra.Basis.Filtration

/-!
# Lower-central weights and adapted bases

Write `C k = LieModule.lowerCentralSeries R L L k`, so `C 0 = L` and `C 1 = [L,L]`.
The bracket satisfies `[C m, C n] ≤ C (m + n + 1)`. Thus a vector in `C (w - 1)` has
lower-central weight at least `w`, and brackets add these positive weights.

For a finite-dimensional nilpotent Lie algebra, `exists_basis_weight_lowerCentralSeries` supplies
a finite ordered basis with positive bounded weights, describing every term of the lower central
series by coordinate vanishing. In particular, a bracket of basis vectors has no coordinate of
weight less than the sum of their weights. This is the weight bound needed to straighten PBW
monomials without lowering weight, and to construct finite weighted enveloping-algebra quotients.
No characteristic or algebraic-closure hypothesis is used.

For a Lie module `M`, a submodule contains the `(k + 1)`-st lower central term of `M` as soon as it
contains every bracket `⁅x, m⁆` with `m` in the `k`-th term
(`TauCeti.toSubmodule_lowerCentralSeries_succ_le`). If `⁅x, y⁆` commutes with `x` and `y`, then it
commutes with the whole span of `x`, `y` and `⁅x, y⁆`, and the bracket of two elements of that span
is a multiple of `⁅x, y⁆` (`TauCeti.lie_lie_eq_zero_of_mem_span` and
`TauCeti.lie_mem_span_singleton_of_mem_span`). The quotient `L ⧸ C k` is nilpotent of class at most
`k`, and a Lie homomorphism into a Lie algebra whose `k`-th lower central term vanishes kills `C k`.
These are the facts used to evaluate universal elements of free nilpotent Lie algebras in a
nilpotent Lie algebra. Every quotient of a nilpotent Lie algebra is nilpotent. Once a term of the
lower central series vanishes, so do all later ones (`LieModule.lowerCentralSeries_eq_bot_of_le`);
for a nilpotent module the series vanishes at its nilpotency length
(`LieModule.lowerCentralSeries_nilpotencyLength_eq_bot`).

## References

* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapters II and V, for the lower central
  series, nilpotent Lie algebras and universal enveloping algebras.
-/

public section

namespace TauCeti

open LieModule Module

section Bracket

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Brackets add lower-central weights. The zero-indexed convention `C 0 = L` accounts for
the extra `1` in the index on the right. -/
theorem lie_lowerCentralSeries_le (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule L M] (m n : ℕ) :
    ⁅lowerCentralSeries R L L m, lowerCentralSeries R L M n⁆ ≤
      lowerCentralSeries R L M (m + n + 1) := by
  induction m generalizing n with
  | zero => simp [lowerCentralSeries_succ]
  | succ m ih =>
    rw [LieSubmodule.lie_le_iff]
    intro x hx y hy
    rw [lowerCentralSeries_succ, ← LieSubmodule.mem_toSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
    -- The scalar is generalized, as `M` is not assumed to be a module over `R` compatible with `L`.
    suffices ∀ r : R, ⁅r • x, y⁆ ∈ lowerCentralSeries R L M (m + 1 + n + 1) by
      simpa using this 1
    refine Submodule.span_induction (p := fun x _ ↦
      ∀ r : R, ⁅r • x, y⁆ ∈ lowerCentralSeries R L M (m + 1 + n + 1)) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a₀, -, b, hb, rfl⟩ r
      rw [← smul_lie]
      generalize r • a₀ = a
      rw [lie_lie]
      apply (lowerCentralSeries R L M _).sub_mem
      · have hby := ih n (LieSubmodule.lie_mem_lie hb hy)
        have ha : ⁅a, ⁅b, y⁆⁆ ∈ lowerCentralSeries R L M ((m + n + 1) + 1) := by
          rw [lowerCentralSeries_succ]
          exact LieSubmodule.lie_mem_lie trivial hby
        simpa only [LieSubmodule.mem_toSubmodule, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using ha
      · have hay : ⁅a, y⁆ ∈ lowerCentralSeries R L M (n + 1) := by
          rw [lowerCentralSeries_succ]
          exact LieSubmodule.lie_mem_lie trivial hy
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (n + 1) (LieSubmodule.lie_mem_lie hb hay)
    · simp
    · intro a b _ _ ha hb r
      simpa [smul_add, add_lie] using (lowerCentralSeries R L M _).add_mem (ha r) (hb r)
    · intro s a _ ha r
      simpa [smul_smul] using ha (r * s)

/-- A submodule contains the `(k + 1)`-st lower central term as soon as it contains every bracket
`⁅x, m⁆` with `m` in the `k`-th term. -/
theorem toSubmodule_lowerCentralSeries_succ_le {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] {N : Submodule R M} {k : ℕ}
    (h : ∀ (x : L), ∀ m ∈ lowerCentralSeries R L M k, ⁅x, m⁆ ∈ N) :
    (lowerCentralSeries R L M (k + 1)).toSubmodule ≤ N := by
  rw [lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', Submodule.span_le]
  rintro _ ⟨x, -, m, hm, rfl⟩
  exact h x m hm

/-- A bracket has zero coordinates below the sum of the weights of its two inputs in a
basis adapted to the lower central series. -/
theorem _root_.Module.Basis.repr_lie_eq_zero_of_weight_lt {ι : Type*}
    (b : Basis ι R L) (w : ι → ℕ)
    (hmem : ∀ k x, x ∈ lowerCentralSeries R L L k ↔
      ∀ i, w i ≤ k → b.repr x i = 0) (i j k : ι) (hk : w k < w i + w j) :
    b.repr ⁅b i, b j⁆ k = 0 := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  have hpos (a : ι) : 0 < w a := by
    refine Nat.pos_of_ne_zero fun h ↦ ?_
    have := (hmem 0 (b a)).mp (by rw [lowerCentralSeries_zero]; trivial) a h.le
    simp at this
  have hb (a : ι) : b a ∈ lowerCentralSeries R L L (w a - 1) := by
    rw [hmem]
    intro c hc
    have hca : c ≠ a := by intro h; subst c; have := hpos a; omega
    simp [hca]
  have hbracket := lie_lowerCentralSeries_le L (w i - 1) (w j - 1)
    (LieSubmodule.lie_mem_lie (hb i) (hb j))
  apply (hmem _ _).mp hbracket k
  have := hpos i
  have := hpos j
  omega

end Bracket

section ClassTwo

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- If `⁅x, y⁆` commutes with `x` and `y`, it commutes with every element of the span of `x`, `y`
and `⁅x, y⁆`. -/
theorem lie_lie_eq_zero_of_mem_span {x y v : L} (hx : ⁅x, ⁅x, y⁆⁆ = 0)
    (hy : ⁅y, ⁅x, y⁆⁆ = 0) (hv : v ∈ Submodule.span R {x, y, ⁅x, y⁆}) : ⁅v, ⁅x, y⁆⁆ = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with hv | hv | hv <;> rw [hv] <;> simp [hx, hy]
  | zero => exact zero_lie _
  | add u v _ _ hu hv => rw [add_lie, hu, hv, add_zero]
  | smul a v _ hv => rw [smul_lie, hv, smul_zero]

/-- If `⁅x, y⁆` commutes with `x` and `y`, the bracket of two elements of the span of `x`, `y` and
`⁅x, y⁆` is a multiple of `⁅x, y⁆`. -/
theorem lie_mem_span_singleton_of_mem_span {x y u v : L} (hx : ⁅x, ⁅x, y⁆⁆ = 0)
    (hy : ⁅y, ⁅x, y⁆⁆ = 0) (hu : u ∈ Submodule.span R {x, y, ⁅x, y⁆})
    (hv : v ∈ Submodule.span R {x, y, ⁅x, y⁆}) : ⁅u, v⁆ ∈ R ∙ ⁅x, y⁆ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    induction hv using Submodule.span_induction with
    | mem v hv =>
      have hzx : ⁅⁅x, y⁆, x⁆ = 0 := by rw [← lie_skew, hx, neg_zero]
      have hzy : ⁅⁅x, y⁆, y⁆ = 0 := by rw [← lie_skew, hy, neg_zero]
      have hyx : ⁅y, x⁆ = -⁅x, y⁆ := by rw [← lie_skew]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rw [hu, hv] <;>
        first
        | exact Submodule.mem_span_singleton_self _
        | exact hyx ▸ neg_mem (Submodule.mem_span_singleton_self _)
        | simp [hx, hy, hzx, hzy]
    | zero => simp
    | add v w _ _ hv hw => rw [lie_add]; exact add_mem hv hw
    | smul a v _ hv => rw [lie_smul]; exact Submodule.smul_mem _ a hv
  | zero => simp
  | add u w _ _ hu hw => rw [add_lie]; exact add_mem hu hw
  | smul a u _ hu => rw [smul_lie]; exact Submodule.smul_mem _ a hu

end ClassTwo

section Quotient

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The quotient of a Lie algebra by the `k`-th term of its lower central series has vanishing
`k`-th lower central term: it is nilpotent of class at most `k`. -/
theorem lowerCentralSeries_quotient_lowerCentralSeries_eq_bot (k : ℕ) :
    lowerCentralSeries R (L ⧸ lowerCentralSeries R L L k) (L ⧸ lowerCentralSeries R L L k) k =
      ⊥ := by
  rw [← LieIdeal.lowerCentralSeries_map_eq k (LieIdeal.surjective_mkQ _), LieIdeal.map_eq_bot_iff,
    LieIdeal.mkQ_ker]

/-- The quotient of a Lie algebra by a term of its lower central series is nilpotent. -/
instance (k : ℕ) : LieRing.IsNilpotent (L ⧸ lowerCentralSeries R L L k) :=
  (isNilpotent_iff R _ _).mpr ⟨k, lowerCentralSeries_quotient_lowerCentralSeries_eq_bot R L k⟩

/-- A quotient of a nilpotent Lie algebra is nilpotent. -/
instance [LieRing.IsNilpotent L] (I : LieIdeal R L) : LieRing.IsNilpotent (L ⧸ I) :=
  (LieIdeal.surjective_mkQ I).lieAlgebra_isNilpotent

end Quotient

section NilpotencyLength

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

omit [LieModule R L M] in
variable {R L M} in
/-- Once a term of the lower central series vanishes, so do all later terms. -/
theorem _root_.LieModule.lowerCentralSeries_eq_bot_of_le {k l : ℕ} (h : k ≤ l)
    (hk : lowerCentralSeries R L M k = ⊥) : lowerCentralSeries R L M l = ⊥ :=
  eq_bot_iff.mpr (hk ▸ LieModule.antitone_lowerCentralSeries R L M h)

/-- The lower central series of a nilpotent Lie module vanishes at its nilpotency length. -/
theorem _root_.LieModule.lowerCentralSeries_nilpotencyLength_eq_bot [LieModule.IsNilpotent L M] :
    lowerCentralSeries R L M (nilpotencyLength L M) = ⊥ := by
  rcases h : nilpotencyLength L M with _ | k
  · rw [nilpotencyLength_eq_zero_iff] at h
    exact ((LieSubmodule.subsingleton_iff R L M).mpr h).elim _ _
  · exact ((nilpotencyLength_eq_succ_iff R L M k).mp h).1

end NilpotencyLength

section Basis

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieRing.IsNilpotent L]

/-- Every finite-dimensional nilpotent Lie algebra has a finite ordered basis with positive
bounded lower-central weights. Each central-series term is described exactly by coordinate
vanishing, and brackets of basis vectors have no coordinates below the sum of their weights. -/
theorem exists_basis_weight_lowerCentralSeries :
    ∃ (N : ℕ) (b : Basis (Fin (Module.finrank K L)) K L)
      (w : Fin (Module.finrank K L) → ℕ),
      (∀ i, 0 < w i ∧ w i ≤ N) ∧
      (∀ k x, x ∈ lowerCentralSeries K L L k ↔ ∀ i, w i ≤ k → b.repr x i = 0) ∧
      ∀ i j k, w k < w i + w j → b.repr ⁅b i, b j⁆ k = 0 := by
  obtain ⟨N, hN⟩ := LieModule.IsNilpotent.nilpotent K L L
  obtain ⟨b, w, hweight, hmem⟩ := exists_basis_weight_of_antitone
    (fun k ↦ (lowerCentralSeries K L L k).toSubmodule)
    (fun _ _ h ↦ antitone_lowerCentralSeries K L L h)
    (by simp) N (by simp [hN])
  exact ⟨N, b, w, hweight, hmem,
    b.repr_lie_eq_zero_of_weight_lt w hmem⟩

end Basis

end TauCeti

namespace LieHom

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/-- A Lie homomorphism into a Lie algebra whose `k`-th lower central term vanishes kills the
`k`-th lower central term of its source. -/
theorem lowerCentralSeries_le_ker (f : L →ₗ⁅R⁆ L') {k : ℕ}
    (hk : LieModule.lowerCentralSeries R L' L' k = ⊥) :
    LieModule.lowerCentralSeries R L L k ≤ f.ker := by
  intro x hx
  have := LieIdeal.map_lowerCentralSeries_le k (f := f) (LieIdeal.mem_map hx)
  rwa [hk, LieSubmodule.mem_bot, ← LieHom.mem_ker] at this

end LieHom
