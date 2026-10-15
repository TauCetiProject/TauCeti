/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Completed.Basic

/-!
# Extending bounded-length maps to completed tensor words

A linear map on finite tensor words extends to their length completion if each output
coordinate depends on a bounded initial segment of the input. Here the bound is uniform:
the output of length `k` depends only on input lengths below `k + 1 + c`. The extension
is defined by finite truncation, agrees with the original map, and sends filtration
degree `n + c` into degree `n`. Over a commutative semiring, any linear map with a
uniform filtration bound and the same values on finite words is equal to this extension,
even if its bound is different.

Composition adds bounds, and square-zero endomorphisms remain square-zero after extension.
These are the linear extension and differential-compatibility steps for completing
finite-arity bar differentials. The coderivation identity and the length bound of a
particular Taylor expansion are separate inputs; arbitrary Taylor maps need not extend
to the length completion.

The length-completion convention follows J.-L. Loday and B. Vallette, *Algebraic Operads*,
Chapters 9--10. The construction uses the finite truncations of `CompletedTensorWords`.
-/

public section

namespace TauCeti.CompletedTensorWords

universe uR uM uN uP

variable {R : Type uR} [CommSemiring R]
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P]

/-- A finite-word map has length bound `c` if its length-`k` output depends only on
input lengths below `k + 1 + c`. Equivalently, it lowers the descending
length filtration by at most `c`. -/
def HasLengthBound (c : ℕ) (f : TensorWords R M →ₗ[R] TensorWords R N) : Prop :=
  ∀ k (x : TensorWords R M), f (truncate R M (k + 1 + c) x) k = f x k

/-- A length bound means that each coordinate is determined by its finite prefix. -/
theorem hasLengthBound_iff (c : ℕ) (f : TensorWords R M →ₗ[R] TensorWords R N) :
    HasLengthBound c f ↔
      ∀ k (x : TensorWords R M), f (truncate R M (k + 1 + c) x) k = f x k :=
  Iff.rfl

/-- Enlarging a length bound preserves coordinate locality. -/
theorem HasLengthBound.mono {c d : ℕ} {f : TensorWords R M →ₗ[R] TensorWords R N}
    (hf : HasLengthBound c f) (hcd : c ≤ d) : HasLengthBound d f := by
  intro k x
  have hcut : k + 1 + c ≤ k + 1 + d := Nat.add_le_add_left hcd _
  rw [← hf k (truncate R M (k + 1 + d) x), truncate_truncate, min_eq_left hcut, hf]

/-- A bounded map has zero length components on inputs beyond its cutoff. -/
theorem HasLengthBound.component_comp_of_eq_zero {c : ℕ}
    {f : TensorWords R M →ₗ[R] TensorWords R N} (hf : HasLengthBound c f)
    (k i : ℕ) (hi : k + 1 + c ≤ i) :
    TensorWords.component R N k ∘ₗ f ∘ₗ TensorWords.of R M i = 0 := by
  apply LinearMap.ext
  intro x
  have ht : truncate R M (k + 1 + c) (TensorWords.of R M i x) = 0 := by
    ext j
    simp only [truncate_apply, DFinsupp.zero_apply]
    by_cases hj : j < k + 1 + c
    · have hij : i ≠ j := by omega
      rw [ite_eq_left hj]
      simpa only [← TensorWords.component_apply] using
        TensorWords.component_of_of_ne R M hij x
    · simp [hj]
  simp only [LinearMap.comp_apply, TensorWords.component_apply, LinearMap.zero_apply]
  rw [← hf k (TensorWords.of R M i x), ht, map_zero, DFinsupp.zero_apply]

/-- A length bound can be checked on individual tensor powers: an input of length at least
`k + 1 + c` contributes nothing to the output of length `k`. -/
theorem hasLengthBound_iff_component_of_eq_zero (c : ℕ)
    (f : TensorWords R M →ₗ[R] TensorWords R N) :
    HasLengthBound c f ↔ ∀ k n, k + 1 + c ≤ n →
      ∀ z : TensorPower R n M, TensorWords.component R N k (f (TensorWords.of R M n z)) = 0 := by
  constructor
  · intro hf k n hn z
    exact LinearMap.congr_fun (hf.component_comp_of_eq_zero k n hn) z
  · intro hf k x
    have h : TensorWords.component R N k ∘ₗ f ∘ₗ truncate R M (k + 1 + c) ∘ₗ
        DFinsupp.coeFnLinearMap R = TensorWords.component R N k ∘ₗ f := by
      apply TensorWords.linearMap_ext R M
      intro n y
      simp only [LinearMap.comp_apply]
      rw [DFinsupp.coeFnLinearMap_apply, truncate_of]
      split_ifs with hn
      · rfl
      · rw [map_zero, map_zero, hf k n (by omega)]
    exact (TensorWords.component_apply R N k _).symm.trans
      ((LinearMap.congr_fun h x).trans (TensorWords.component_apply R N k _))

/-- Construct a linear map on completed tensor words by reading each output coordinate
from a finite truncation of the input. It agrees with `f` on finite words when `f` has
length bound `c`. -/
noncomputable def extend (c : ℕ) (f : TensorWords R M →ₗ[R] TensorWords R N) :
    CompletedTensorWords R M →ₗ[R] CompletedTensorWords R N :=
  LinearMap.pi fun k ↦ TensorWords.component R N k ∘ₗ f ∘ₗ truncate R M (k + 1 + c)

/-- Each coordinate of the extension is computed from a finite input prefix. -/
@[simp]
theorem extend_apply (c : ℕ) (f : TensorWords R M →ₗ[R] TensorWords R N)
    (x : CompletedTensorWords R M) (k : ℕ) :
    extend c f x k = f (truncate R M (k + 1 + c) x) k := by
  simp [extend]

/-- The extension agrees with the original map on finite tensor words. -/
@[simp]
theorem extend_coe (c : ℕ) (f : TensorWords R M →ₗ[R] TensorWords R N)
    (hf : HasLengthBound c f) (x : TensorWords R M) :
    extend c f x = (f x : CompletedTensorWords R N) := by
  funext k
  simpa only [extend_apply] using hf k x

/-- Any longer finite prefix computes the same output coordinate. -/
theorem extend_apply_eq_of_le (c : ℕ) (f : TensorWords R M →ₗ[R] TensorWords R N)
    (hf : HasLengthBound c f) (x : CompletedTensorWords R M) (k n : ℕ)
    (hkn : k + 1 + c ≤ n) :
    extend c f x k = f (truncate R M n x) k := by
  rw [← hf k (truncate R M n x), truncate_truncate, min_eq_left hkn, extend_apply]

/-- Truncating an extended value can be computed from one finite input prefix. -/
theorem truncate_extend (c : ℕ) (f : TensorWords R M →ₗ[R] TensorWords R N)
    (hf : HasLengthBound c f) (x : CompletedTensorWords R M) (n : ℕ) :
    truncate R N n (extend c f x) = truncate R N n (f (truncate R M (n + c) x)) := by
  ext k
  rw [truncate_apply, truncate_apply]
  by_cases hk : k < n
  · simp only [ite_eq_left hk]
    exact extend_apply_eq_of_le c f hf x k (n + c) (by omega)
  · simp only [ite_eq_right hk]

/-- The completed extension lowers the descending length filtration by at most its bound. -/
theorem map_extend_filtration_le (c : ℕ)
    (f : TensorWords R M →ₗ[R] TensorWords R N) (n : ℕ) :
    Submodule.map (extend c f) (filtration R M (n + c)) ≤ filtration R N n := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, mem_filtration] at hx ⊢
  intro k hk
  have ht : truncate R M (k + 1 + c) x = 0 := by
    ext j
    by_cases hj : j < k + 1 + c
    · simp only [truncate_apply, ite_eq_left hj, DFinsupp.zero_apply]
      exact hx j (by omega)
    · simp [truncate_apply, hj]
  rw [extend_apply, ht, map_zero, DFinsupp.zero_apply]

/-- Identity on finite words has every nonnegative length bound. -/
@[simp]
theorem hasLengthBound_id (c : ℕ) : HasLengthBound c (LinearMap.id : TensorWords R M →ₗ[R] _) := by
  intro k x
  have hk : k < k + 1 + c := by omega
  simp [truncate_apply, hk]

/-- Letterwise maps preserve length and hence have length bound zero. -/
@[simp]
theorem hasLengthBound_map (f : M →ₗ[R] N) : HasLengthBound 0 (TensorWords.map f) := by
  intro k x
  have hk : k < k + 1 + 0 := by omega
  rw [← TensorWords.component_apply, ← TensorWords.component_apply,
    TensorWords.component_map, TensorWords.component_map]
  simp only [TensorWords.component_apply, truncate_apply, ite_eq_left hk]

/-- Zero has every length bound. -/
@[simp]
theorem hasLengthBound_zero (c : ℕ) :
    HasLengthBound c (0 : TensorWords R M →ₗ[R] TensorWords R N) := by
  intro k x
  simp

/-- Adding finite-word maps with a common length bound preserves that bound. -/
theorem HasLengthBound.add {c : ℕ}
    {f g : TensorWords R M →ₗ[R] TensorWords R N}
    (hf : HasLengthBound c f) (hg : HasLengthBound c g) : HasLengthBound c (f + g) := by
  intro k x
  simp only [LinearMap.add_apply, DirectSum.add_apply, hf k x, hg k x]

/-- Scaling a finite-word map preserves its length bound. -/
theorem HasLengthBound.smul {c : ℕ} {f : TensorWords R M →ₗ[R] TensorWords R N}
    (hf : HasLengthBound c f) (r : R) : HasLengthBound c (r • f) := by
  intro k x
  simp only [LinearMap.smul_apply, DirectSum.smul_apply, hf k x]

/-- The finite-prefix construction preserves addition at a common cutoff. -/
@[simp]
theorem extend_add (c : ℕ) (f g : TensorWords R M →ₗ[R] TensorWords R N) :
    extend c (f + g) = extend c f + extend c g := by
  ext x k
  simp only [extend_apply, LinearMap.add_apply, DirectSum.add_apply, Pi.add_apply]

/-- The finite-prefix construction preserves scalar multiplication at a fixed cutoff. -/
@[simp]
theorem extend_smul (c : ℕ) (r : R) (f : TensorWords R M →ₗ[R] TensorWords R N) :
    extend c (r • f) = r • extend c f := by
  ext x k
  simp only [extend_apply, LinearMap.smul_apply, DirectSum.smul_apply, Pi.smul_apply]

/-- Extending the identity gives the identity on the completion. -/
@[simp]
theorem extend_id (c : ℕ) :
    extend c (LinearMap.id : TensorWords R M →ₗ[R] _) = LinearMap.id := by
  ext x k
  have hk : k < k + 1 + c := by omega
  simp [truncate_apply, hk]

/-- Extending zero gives zero on the completion. -/
@[simp]
theorem extend_zero (c : ℕ) :
    extend c (0 : TensorWords R M →ₗ[R] TensorWords R N) = 0 := by
  ext x k
  simp

/-- Composing finite-word maps adds their length bounds. -/
theorem HasLengthBound.comp {c d : ℕ}
    {f : TensorWords R M →ₗ[R] TensorWords R N}
    {g : TensorWords R N →ₗ[R] TensorWords R P}
    (hg : HasLengthBound d g) (hf : HasLengthBound c f) :
    HasLengthBound (c + d) (g ∘ₗ f) := by
  intro k x
  simp only [LinearMap.comp_apply]
  have h : truncate R N (k + 1 + d) (f (truncate R M (k + 1 + (c + d)) x)) =
      truncate R N (k + 1 + d) (f x) := by
    ext j
    simp only [truncate_apply]
    by_cases hj : j < k + 1 + d
    · simp only [ite_eq_left hj]
      rw [← hf j (truncate R M (k + 1 + (c + d)) x), truncate_truncate,
        min_eq_left (by omega), hf]
    · simp only [ite_eq_right hj]
  rw [← hg k (f (truncate R M (k + 1 + (c + d)) x)), h, hg]

/-- Extending a composite agrees with composing the extensions. -/
@[simp]
theorem extend_comp {c d : ℕ}
    {f : TensorWords R M →ₗ[R] TensorWords R N}
    {g : TensorWords R N →ₗ[R] TensorWords R P}
    (hg : HasLengthBound d g) (hf : HasLengthBound c f) :
    extend (c + d) (g ∘ₗ f) = extend d g ∘ₗ extend c f := by
  ext x k
  simp only [LinearMap.comp_apply, extend_apply]
  rw [truncate_extend c f hf]
  rw [← hg k (f (truncate R M (k + 1 + (c + d)) x))]
  have hcut : k + 1 + (c + d) = (k + 1 + d) + c := by omega
  rw [hcut]

/-- The extension is independent of the bound used to construct it. -/
theorem extend_eq (c d : ℕ) (f : TensorWords R M →ₗ[R] TensorWords R N)
    (hc : HasLengthBound c f) (hd : HasLengthBound d f) :
    extend c f = extend d f := by
  ext x k
  exact (extend_apply_eq_of_le c f hc x k (k + 1 + max c d) (by omega)).trans
    (extend_apply_eq_of_le d f hd x k (k + 1 + max c d) (by omega)).symm

/-- The coordinate locality condition is equivalent to lowering the
descending length filtration by at most `c` on finite words. -/
theorem hasLengthBound_iff_truncate_eq_zero (c : ℕ)
    (f : TensorWords R M →ₗ[R] TensorWords R N) :
    HasLengthBound c f ↔ ∀ n (x : TensorWords R M),
      truncate R M (n + c) x = 0 → truncate R N n (f x) = 0 := by
  constructor
  · intro hf n x hx
    ext k
    rw [truncate_apply, DFinsupp.zero_apply]
    by_cases hk : k < n
    · rw [ite_eq_left hk, ← hf k x]
      have ht : truncate R M (k + 1 + c) x = 0 := by
        have hcut : k + 1 + c ≤ n + c := by omega
        rw [← min_eq_left hcut, ← truncate_truncate,
          hx, DFinsupp.coe_zero, map_zero]
      rw [ht, map_zero, DFinsupp.zero_apply]
    · rw [ite_eq_right hk]
  · intro hf k x
    let t : TensorWords R M := x.filter fun j ↦ ¬j < k + 1 + c
    have ht : truncate R M (k + 1 + c) t = 0 := by
      ext j
      by_cases hj : j < k + 1 + c <;> simp [t, truncate_apply, hj]
    have hprefix : truncate R M (k + 1 + c) x = x.filter (fun j ↦ j < k + 1 + c) := by
      ext j
      simp only [truncate_apply, DFinsupp.filter_apply]
    have hx : truncate R M (k + 1 + c) x + t = x := by
      rw [hprefix]
      exact DFinsupp.filter_add_filter_not x (fun j ↦ j < k + 1 + c)
    have h := congrArg (fun z : TensorWords R N ↦ z k) (hf (k + 1) t ht)
    have hf0 : f t k = 0 := by
      simpa only [truncate_apply, Nat.lt_succ_self, ite_true, DFinsupp.zero_apply] using h
    simpa only [map_add, DirectSum.add_apply, hf0, add_zero] using
      congrArg (fun z : TensorWords R M ↦ f z k) hx

/-- A linear map with a uniform filtration bound is determined by its finite-word values.
The bounds of the two maps may differ. -/
theorem _root_.LinearMap.eq_of_coe_eq_of_filtration_bound
    (f g : CompletedTensorWords R M →ₗ[R] CompletedTensorWords R N) (c d : ℕ)
    (hf : ∀ n, Submodule.map f (filtration R M (n + c)) ≤ filtration R N n)
    (hg : ∀ n, Submodule.map g (filtration R M (n + d)) ≤ filtration R N n)
    (hfg : ∀ x : TensorWords R M,
      f (DFinsupp.coeFnLinearMap R x) = g (DFinsupp.coeFnLinearMap R x)) : f = g := by
  ext x k
  let n := k + 1 + max c d
  let t : CompletedTensorWords R M := fun j ↦ if j < n then 0 else x j
  have hx : DFinsupp.coeFnLinearMap R (truncate R M n x) + t = x := by
    funext j
    by_cases hj : j < n <;> simp [t, truncate_apply, hj]
  have ht : t ∈ filtration R M n := by
    rw [mem_filtration]
    intro j hj
    simp [t, hj]
  have htf : t ∈ filtration R M (k + 1 + c) :=
    filtration_antitone R M (by dsimp [n]; omega) ht
  have htg : t ∈ filtration R M (k + 1 + d) :=
    filtration_antitone R M (by dsimp [n]; omega) ht
  have hf0 := (mem_filtration R N _ _).mp
    (hf (k + 1) ⟨_, htf, rfl⟩) k (Nat.lt_succ_self k)
  have hg0 := (mem_filtration R N _ _).mp
    (hg (k + 1) ⟨_, htg, rfl⟩) k (Nat.lt_succ_self k)
  rw [← hx, map_add, map_add, Pi.add_apply, Pi.add_apply, hf0, hg0, add_zero,
    add_zero, hfg]

/-- The extension is the unique linear map agreeing on finite words and admitting a
uniform filtration bound. -/
theorem extend_unique (c : ℕ) (f : TensorWords R M →ₗ[R] TensorWords R N)
    (hf : HasLengthBound c f)
    (g : CompletedTensorWords R M →ₗ[R] CompletedTensorWords R N) (d : ℕ)
    (hg : ∀ n, Submodule.map g (filtration R M (n + d)) ≤ filtration R N n)
    (hgf : ∀ x, g (DFinsupp.coeFnLinearMap R x) = DFinsupp.coeFnLinearMap R (f x)) :
    g = extend c f := by
  apply LinearMap.eq_of_coe_eq_of_filtration_bound g (extend c f) d c hg
    (map_extend_filtration_le c f)
  intro x
  rw [hgf]
  simpa only [DFinsupp.coeFnLinearMap_apply] using (extend_coe c f hf x).symm

/-- A square-zero finite-word endomorphism remains square-zero on the length completion. -/
theorem extend_comp_self_eq_zero (c : ℕ) (f : TensorWords R M →ₗ[R] TensorWords R M)
    (hf : HasLengthBound c f) (hsq : f ∘ₗ f = 0) :
    extend c f ∘ₗ extend c f = 0 := by
  rw [← extend_comp hf hf]
  ext x k
  rw [extend_apply]
  exact congrArg (fun z : TensorWords R M ↦ z k)
    (LinearMap.congr_fun hsq (truncate R M (k + 1 + (c + c)) x))

end TauCeti.CompletedTensorWords
