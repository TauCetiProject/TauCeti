/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import TauCeti.LinearAlgebra.Graded.LinearMap
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.BigOperators
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Locally nilpotent endomorphisms and families of endomorphisms

An endomorphism `f` of a module is *locally nilpotent* when every vector is annihilated by some
power of `f`.  Then `1 + f` is invertible.  No global nilpotence bound is needed, so the statement
applies to operators which lower a filtration by direct summands without being nilpotent on the
whole module, such as those of homological perturbation theory on bar constructions.

Over a `ℚ`-algebra, a locally nilpotent endomorphism also has an exponential
`exp f x = ∑ fᵏ x / k!`, a finite sum for each `x`. It is a linear automorphism with inverse
`exp (-f)`, again with no global nilpotence bound. This is what exponentiates the adjoint action of
a raising generator on an infinite-dimensional Lie algebra presented by generators and relations.

On a free module `ι →₀ R`, an endomorphism is locally nilpotent as soon as it strictly lowers a
weight on the basis whose strict order is well-founded, for instance any weight on a finite basis.

More generally, a family `f i` of endomorphisms is locally nilpotent when every vector is killed by
all sufficiently long composites `f i₁ ∘ ⋯ ∘ f i_d`. The vectors killed by all composites of
length `d` form a submodule `Module.End.wordKer f d`, and local nilpotence is the statement
`⨆ d, Module.End.wordKer f d = ⊤`. It passes to submodules and quotients stable under the family.
If no nonzero vector is killed by every `f i`, then `Module.End.wordKer f d = ⊥` for every `d`, so
a locally nilpotent family with this property can only act on the zero module. Operators lowering
a grading by `ℕ`, such as divided differences on a polynomial ring, form locally nilpotent families.

## Main results

* `Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero`: `1 + f` is a unit when `f` is
  locally nilpotent.
* `TauCeti.LinearMap.IsHomogeneous.ringInverse_one_add`: the inverse of `1 + f` has degree zero
  when `f` is locally nilpotent of degree zero.
* `Module.End.locallyNilpotentExp`: the exponential of a locally nilpotent endomorphism, as a linear
  automorphism; `Module.End.locallyNilpotentExp_apply_eq_sum` computes it as a finite sum and
  `Module.End.symm_locallyNilpotentExp` identifies its inverse with `exp (-f)`.
* `Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt`: an endomorphism of `ι →₀ R`
  that strictly lowers a well-founded weight on the basis is locally nilpotent.
* `Module.End.mem_wordKer_iff`: `Module.End.wordKer f d` consists of the vectors killed by the
  composite of every word of length `d` in the family `f`.
* `Module.End.wordKer_eq_bot_of_iInf_ker_eq_bot`: if the family `f` has no common nonzero kernel
  vector, then neither do its composites of any length.
* `Module.End.iSup_wordKer_eq_top_of_surjective`, `Module.End.iSup_wordKer_eq_top_of_injective`:
  local nilpotence of a family passes to quotients and to submodules.
-/

public section

variable {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]

/-- If every vector is annihilated by some power of `f`, then `1 + f` is invertible. -/
theorem Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero (f : Module.End R M)
    (hf : ∀ x, ∃ n, (f ^ n) x = 0) : IsUnit (1 + f) := by
  have hneg : ∀ (n : ℕ) (x : M), (f ^ n) x = 0 → ((-f) ^ n) x = 0 := by
    intro n x hx
    rw [neg_pow, Module.End.mul_apply, hx, map_zero]
  rw [Module.End.isUnit_iff]
  refine ⟨(injective_iff_map_eq_zero (1 + f)).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨n, hn⟩ := hf x
    have h := LinearMap.congr_fun (geom_sum_mul_neg (-f) n) x
    rw [sub_neg_eq_add, Module.End.mul_apply, hx, map_zero, LinearMap.sub_apply,
      Module.End.one_apply, hneg n x hn, sub_zero] at h
    exact h.symm
  · obtain ⟨n, hn⟩ := hf y
    refine ⟨(∑ i ∈ Finset.range n, (-f) ^ i) y, ?_⟩
    have h := LinearMap.congr_fun (mul_neg_geom_sum (-f) n) y
    rwa [sub_neg_eq_add, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      hneg n y hn, sub_zero] at h


section Ring

variable {S N : Type*} [Ring S] [AddCommGroup N] [Module S N]

/-- If `f` is locally nilpotent and homogeneous of degree zero for a grading by submodules, then so
is the inverse of `1 + f`: on a homogeneous vector it is a finite geometric series in `-f`. -/
theorem TauCeti.LinearMap.IsHomogeneous.ringInverse_one_add {ι : Type*} [AddMonoid ι]
    {𝒜 : ι → Submodule S N} {f : Module.End S N}
    (hf : TauCeti.LinearMap.IsHomogeneous f 𝒜 𝒜 0) (hnil : ∀ x, ∃ n, (f ^ n) x = 0) :
    TauCeti.LinearMap.IsHomogeneous (Ring.inverse (1 + f)) 𝒜 𝒜 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  obtain ⟨n, hn⟩ := hnil x
  have hpow : ∀ i : ℕ, ((-f) ^ i) x ∈ 𝒜 p := by
    intro i
    induction i with
    | zero => simpa using hx
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply]
      simpa only [add_zero] using neg_mem (hf.map_mem ih)
  set y := (∑ i ∈ Finset.range n, (-f) ^ i) x with hy_def
  have hy : (1 + f) y = x := by
    have h := LinearMap.congr_fun (mul_neg_geom_sum (-f) n) x
    rwa [sub_neg_eq_add, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      neg_pow, Module.End.mul_apply, hn, map_zero, sub_zero] at h
  have hinv : Ring.inverse (1 + f) x = y := by
    rw [← hy, ← Module.End.mul_apply,
      Ring.inverse_mul_cancel _ (Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero f
        hnil), Module.End.one_apply]
  rw [hinv, add_zero, hy_def, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ ↦ hpow i

end Ring

section Finsupp

open Finsupp

variable {R ι α : Type*} [Semiring R] [LT α]

/-- **Strictly lowering a well-founded weight on a basis is locally nilpotent.** Let `w` be a
weight on `ι` whose strict order `w j < w i` is well-founded, as is automatic when `ι` is finite
and `α` is a preorder, or when `<` is well-founded on `α`. If an endomorphism `f` of `ι →₀ R`
sends each basis vector `single i 1` into the span of the basis vectors of strictly smaller
weight, then every vector is killed by a power of `f`. -/
theorem Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt
    (f : Module.End R (ι →₀ R)) (w : ι → α) (hw : WellFounded (InvImage (· < ·) w))
    (hf : ∀ i, ∀ j ∈ (f (single i 1)).support, w j < w i) (x : ι →₀ R) :
    ∃ k, (f ^ k) x = 0 := by
  let N : Submodule R (ι →₀ R) :=
    { carrier := {x | ∃ k, (f ^ k) x = 0}
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨max a b, ?_⟩
        rw [map_add, Module.End.pow_map_zero_of_le (le_max_left _ _) ha,
          Module.End.pow_map_zero_of_le (le_max_right _ _) hb, add_zero]
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := by
        rintro c x ⟨a, ha⟩
        exact ⟨a, by rw [map_smul, ha, smul_zero]⟩ }
  have hN : ∀ x, x ∈ N ↔ ∃ k, (f ^ k) x = 0 := fun _ ↦ Iff.rfl
  -- Well-founded induction on the weight: `f (single i 1)` involves only basis vectors of
  -- smaller weight, each of which is killed by a power of `f` by induction.
  have hsingle : ∀ i, single i (1 : R) ∈ N := by
    intro i
    induction i using hw.induction with
    | _ i ih =>
      have hfi : f (single i 1) ∈ N := by
        rw [← Finsupp.sum_single (f (single i 1))]
        refine Submodule.sum_mem _ fun j hj ↦ ?_
        rw [← Finsupp.smul_single_one]
        exact N.smul_mem _ (ih j (hf i j hj))
      obtain ⟨k, hk⟩ := (hN _).1 hfi
      exact (hN _).2 ⟨k + 1, by rw [pow_succ, Module.End.mul_apply, hk]⟩
  have hx : x ∈ N := by
    induction x using Finsupp.induction_linear with
    | zero => exact N.zero_mem
    | add x y hx hy => exact N.add_mem hx hy
    | single i c =>
      rw [← Finsupp.smul_single_one]
      exact N.smul_mem _ (hsingle i)
  exact (hN x).1 hx

end Finsupp

section Family

namespace Module.End

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- The submodule of vectors killed by every composite `f i₁ ∘ ⋯ ∘ f i_d` of `d` members of a
family `f` of endomorphisms (`Module.End.mem_wordKer_iff`). Only `0` is killed by the empty
composite, and `x` is killed by all composites of length `d + 1` exactly when every `f i x` is
killed by all composites of length `d` (`Module.End.mem_wordKer_succ`).

These submodules increase with `d` (`Module.End.monotone_wordKer`). The family is *locally
nilpotent* when they exhaust the module, `⨆ d, wordKer f d = ⊤`: every vector is killed by all
sufficiently long composites (`Module.End.iSup_wordKer_eq_top_iff`). -/
def wordKer (f : ι → Module.End R M) : ℕ → Submodule R M
  | 0 => ⊥
  | d + 1 => ⨅ i, (wordKer f d).comap (f i)

variable (f : ι → Module.End R M)

/-- Only `0` is killed by the empty composite. -/
@[simp]
theorem wordKer_zero : wordKer f 0 = ⊥ :=
  (rfl)

/-- The recursive description of `wordKer f (d + 1)`. -/
theorem wordKer_succ (d : ℕ) : wordKer f (d + 1) = ⨅ i, (wordKer f d).comap (f i) :=
  (rfl)

/-- A vector is killed by all composites of length `d + 1` exactly when its image under every
member of the family is killed by all composites of length `d`. -/
@[simp]
theorem mem_wordKer_succ {d : ℕ} {x : M} : x ∈ wordKer f (d + 1) ↔ ∀ i, f i x ∈ wordKer f d := by
  simp only [wordKer_succ, Submodule.mem_iInf, Submodule.mem_comap]

/-- A vector lies in `wordKer f d` exactly when it is killed by the composite of every word of
length `d` in the family `f`. -/
theorem mem_wordKer_iff {d : ℕ} {x : M} :
    x ∈ wordKer f d ↔ ∀ w : List ι, w.length = d → (w.map f).prod x = 0 := by
  induction d generalizing x with
  | zero => simp [List.length_eq_zero_iff]
  | succ d ih =>
    simp only [mem_wordKer_succ, ih]
    refine ⟨fun h w hw ↦ ?_, fun h i w hw ↦ ?_⟩
    · obtain rfl | ⟨w, i, rfl⟩ := w.eq_nil_or_concat
      · simp at hw
      · simp only [List.concat_eq_append, List.length_append, List.length_singleton,
          Nat.add_right_cancel_iff] at hw
        simpa [Module.End.mul_apply] using h i w hw
    · simpa [Module.End.mul_apply] using h (w ++ [i]) (by simp [hw])

/-- A vector killed by all composites of length `d` is killed by all longer composites. -/
theorem monotone_wordKer : Monotone (wordKer f) := by
  refine monotone_nat_of_le_succ fun d ↦ ?_
  induction d with
  | zero => exact bot_le
  | succ d ih => exact iInf_mono fun i ↦ Submodule.comap_mono ih

/-- The family `f` is locally nilpotent, `⨆ d, wordKer f d = ⊤`, exactly when every vector is
killed by all composites of some length. -/
theorem iSup_wordKer_eq_top_iff : ⨆ d, wordKer f d = ⊤ ↔ ∀ x, ∃ d, x ∈ wordKer f d := by
  simp only [Submodule.eq_top_iff', Submodule.mem_iSup_of_directed _
    (monotone_wordKer f).directed_le]

/-- If no nonzero vector is killed by every member of the family, then no nonzero vector is killed
by all composites of a given length. -/
theorem wordKer_eq_bot_of_iInf_ker_eq_bot (hf : ⨅ i, LinearMap.ker (f i) = ⊥) (d : ℕ) :
    wordKer f d = ⊥ := by
  induction d with
  | zero => exact wordKer_zero f
  | succ d ih => simp only [wordKer_succ, ih, Submodule.comap_bot, hf]

/-- For a nonempty family all of whose members equal `g`, `wordKer` is the kernel of `g ^ d`. -/
theorem wordKer_const [Nonempty ι] (g : Module.End R M) (d : ℕ) :
    wordKer (fun _ : ι ↦ g) d = LinearMap.ker (g ^ d) := by
  induction d with
  | zero => rw [wordKer_zero, pow_zero, Module.End.one_eq_id, LinearMap.ker_id]
  | succ d ih => rw [wordKer_succ, ih, iInf_const, pow_succ, Module.End.mul_eq_comp,
      LinearMap.ker_comp]

variable {f} {f' : ι → Module.End R N} {g : M →ₗ[R] N}

/-- A linear map intertwining two families of endomorphisms maps `wordKer f d` into
`wordKer f' d`. -/
theorem map_wordKer_le (hg : ∀ i, g ∘ₗ f i = f' i ∘ₗ g) (d : ℕ) :
    (wordKer f d).map g ≤ wordKer f' d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_wordKer_succ] at hx
    rw [mem_wordKer_succ]
    intro i
    rw [← LinearMap.comp_apply, ← hg i, LinearMap.comp_apply]
    exact ih (Submodule.mem_map_of_mem (hx i))

/-- An injective linear map intertwining two families of endomorphisms pulls `wordKer f' d` back to
`wordKer f d`. -/
theorem comap_wordKer_of_injective (hg : ∀ i, g ∘ₗ f i = f' i ∘ₗ g)
    (hinj : Function.Injective g) (d : ℕ) : (wordKer f' d).comap g = wordKer f d := by
  induction d with
  | zero => simpa using LinearMap.ker_eq_bot_of_injective hinj
  | succ d ih =>
    ext x
    simp only [Submodule.mem_comap, mem_wordKer_succ]
    refine forall_congr' fun i ↦ ?_
    rw [← ih, Submodule.mem_comap, ← LinearMap.comp_apply g, hg i, LinearMap.comp_apply]

/-- Local nilpotence passes to quotients: the image of a locally nilpotent family under a
surjective intertwining linear map is locally nilpotent. -/
theorem iSup_wordKer_eq_top_of_surjective (hg : ∀ i, g ∘ₗ f i = f' i ∘ₗ g)
    (hsurj : Function.Surjective g) (hf : ⨆ d, wordKer f d = ⊤) : ⨆ d, wordKer f' d = ⊤ := by
  rw [eq_top_iff, ← LinearMap.range_eq_top.2 hsurj, LinearMap.range_eq_map, ← hf,
    Submodule.map_iSup]
  exact iSup_mono (map_wordKer_le hg)

/-- Local nilpotence passes to submodules: a family intertwined by an injective linear map with a
locally nilpotent family is locally nilpotent. -/
theorem iSup_wordKer_eq_top_of_injective (hg : ∀ i, g ∘ₗ f i = f' i ∘ₗ g)
    (hinj : Function.Injective g) (hf' : ⨆ d, wordKer f' d = ⊤) : ⨆ d, wordKer f d = ⊤ := by
  rw [iSup_wordKer_eq_top_iff] at hf' ⊢
  intro x
  obtain ⟨d, hd⟩ := hf' (g x)
  exact ⟨d, comap_wordKer_of_injective hg hinj d ▸ hd⟩

end Module.End

end Family

section Exp

/-! ### The exponential of a locally nilpotent endomorphism -/

open Finset

namespace Module.End

variable {R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Module R M]

/-- The exponential series of `f` at `x`, truncated at a power of `f` killing `x`. Beyond the first
such power every term vanishes, so the truncation point does not matter
(`Module.End.sum_range_inv_factorial_smul_pow_apply_eq`). -/
private noncomputable def locallyNilpotentExpFun (f : Module.End R M)
    (hf : ∀ x, ∃ n, (f ^ n) x = 0) (x : M) : M :=
  ∑ k ∈ range (hf x).choose, algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (f ^ k) x

/-- Extending a truncated exponential series past a power of `f` killing `x` adds only zeros. -/
private theorem sum_range_inv_factorial_smul_pow_apply_of_le (f : Module.End R M) {x : M}
    {n m : ℕ} (hn : (f ^ n) x = 0) (hnm : n ≤ m) :
    ∑ k ∈ range m, algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (f ^ k) x =
      ∑ k ∈ range n, algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (f ^ k) x := by
  refine (sum_subset (range_subset_range.2 hnm) fun k _ hk => ?_).symm
  rw [mem_range, not_lt] at hk
  rw [Module.End.pow_map_zero_of_le hk hn, smul_zero]

/-- Two truncations of the exponential series at powers of `f` killing `x` agree. -/
private theorem sum_range_inv_factorial_smul_pow_apply_eq (f : Module.End R M) {x : M}
    {n m : ℕ} (hn : (f ^ n) x = 0) (hm : (f ^ m) x = 0) :
    ∑ k ∈ range n, algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (f ^ k) x =
      ∑ k ∈ range m, algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (f ^ k) x := by
  rcases le_total n m with h | h
  · exact (sum_range_inv_factorial_smul_pow_apply_of_le f hn h).symm
  · exact sum_range_inv_factorial_smul_pow_apply_of_le f hm h

private theorem locallyNilpotentExpFun_eq_sum (f : Module.End R M)
    (hf : ∀ x, ∃ n, (f ^ n) x = 0) {x : M} {n : ℕ} (hn : (f ^ n) x = 0) :
    locallyNilpotentExpFun f hf x =
      ∑ k ∈ range n, algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (f ^ k) x :=
  sum_range_inv_factorial_smul_pow_apply_eq f (hf x).choose_spec hn

/-- The exponential series of a locally nilpotent endomorphism, as a linear map. -/
private noncomputable def locallyNilpotentExpLinearMap (f : Module.End R M)
    (hf : ∀ x, ∃ n, (f ^ n) x = 0) : Module.End R M where
  toFun := locallyNilpotentExpFun f hf
  map_add' x y := by
    obtain ⟨n, hn⟩ := hf x
    obtain ⟨m, hm⟩ := hf y
    have hx : (f ^ (n + m)) x = 0 := Module.End.pow_map_zero_of_le (Nat.le_add_right n m) hn
    have hy : (f ^ (n + m)) y = 0 := Module.End.pow_map_zero_of_le (Nat.le_add_left m n) hm
    rw [locallyNilpotentExpFun_eq_sum f hf hx, locallyNilpotentExpFun_eq_sum f hf hy,
      locallyNilpotentExpFun_eq_sum f hf (by rw [map_add, hx, hy, add_zero]), ← sum_add_distrib]
    simp only [map_add, smul_add]
  map_smul' r x := by
    obtain ⟨n, hn⟩ := hf x
    rw [locallyNilpotentExpFun_eq_sum f hf hn,
      locallyNilpotentExpFun_eq_sum f hf (by rw [map_smul, hn, smul_zero]), smul_sum]
    simp only [map_smul, RingHom.id_apply, smul_comm r]

omit [Algebra ℚ R] in
/-- Local nilpotence passes from `f` to `-f`. -/
private theorem neg_pow_apply_eq_zero (f : Module.End R M) {x : M} {n : ℕ}
    (hn : (f ^ n) x = 0) : ((-f) ^ n) x = 0 := by
  rw [neg_pow, Module.End.mul_apply, hn, map_zero]

omit [Algebra ℚ R] in
/-- Powers of `-f` are powers of `f` up to sign. -/
private theorem neg_pow_apply (f : Module.End R M) (n : ℕ) (x : M) :
    ((-f) ^ n) x = (-1 : R) ^ n • (f ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.neg_apply, pow_succ' f,
      Module.End.mul_apply, pow_succ', neg_one_mul, neg_smul, smul_neg]

/-- The coefficients of `exp X * exp (-X)`: for `m > 0` the alternating sum of
`1 / (i ! j !)` over `i + j = m` vanishes, since it is `(1 - 1) ^ m / m !`. -/
private theorem sum_antidiagonal_inv_factorial_mul_neg_one_pow (m : ℕ) :
    ∑ ij ∈ antidiagonal m,
        (ij.1.factorial : ℚ)⁻¹ * ((ij.2.factorial : ℚ)⁻¹ * (-1) ^ ij.2) =
      if m = 0 then 1 else 0 := by
  have h := (Commute.all (1 : ℚ) (-1)).add_pow' m
  rw [add_neg_cancel, zero_pow_eq] at h
  have hterm : ∀ ij ∈ antidiagonal m,
      (ij.1.factorial : ℚ)⁻¹ * ((ij.2.factorial : ℚ)⁻¹ * (-1) ^ ij.2) =
        (m.factorial : ℚ)⁻¹ * (m.choose ij.1 • ((1 : ℚ) ^ ij.1 * (-1) ^ ij.2)) := by
    intro ij hij
    rw [mem_antidiagonal] at hij
    subst m
    rw [nsmul_eq_mul, one_pow, one_mul]
    have hfac : ((ij.1 + ij.2).choose ij.1 : ℚ) * ij.2.factorial * ij.1.factorial =
        (ij.1 + ij.2).factorial := by
      have := Nat.add_choose_mul_factorial_mul_factorial ij.2 ij.1
      rw [Nat.add_comm ij.2] at this
      exact_mod_cast this
    field_simp
    rw [← hfac]
    ring
  rw [sum_congr rfl hterm, ← mul_sum, ← h]
  split_ifs with hm <;> simp [hm]

/-- `exp (-f)` is a left inverse of `exp f`. -/
private theorem locallyNilpotentExpLinearMap_neg_apply (f : Module.End R M)
    (hf : ∀ x, ∃ n, (f ^ n) x = 0) (hf' : ∀ x, ∃ n, ((-f) ^ n) x = 0) (x : M) :
    locallyNilpotentExpLinearMap f hf (locallyNilpotentExpLinearMap (-f) hf' x) = x := by
  obtain ⟨n, hn⟩ := hf x
  have hn1 : (f ^ (n + 1)) x = 0 := Module.End.pow_map_zero_of_le (Nat.le_succ n) hn
  -- every `f ^ j x` is killed by `f ^ (n + 1)`, so all inner series can be truncated there
  have hkill : ∀ j, (f ^ (n + 1)) ((f ^ j) x) = 0 := fun j => by
    rw [← Module.End.mul_apply, ← pow_add, add_comm, pow_add, Module.End.mul_apply, hn1,
      map_zero]
  let g : ℕ × ℕ → M := fun ij =>
    (algebraMap ℚ R ((ij.1.factorial : ℚ)⁻¹ * ((ij.2.factorial : ℚ)⁻¹ * (-1) ^ ij.2))) •
      (f ^ (ij.1 + ij.2)) x
  have hg : ∀ i j, n + 1 ≤ i ∨ n + 1 ≤ j → g (i, j) = 0 := fun i j hij => by
    have : n + 1 ≤ i + j := by omega
    simp only [g, Module.End.pow_map_zero_of_le this hn1, smul_zero]
  change locallyNilpotentExpLinearMap f hf (locallyNilpotentExpFun (-f) hf' x) = x
  rw [locallyNilpotentExpFun_eq_sum (-f) hf' (neg_pow_apply_eq_zero f hn1), map_sum]
  calc ∑ j ∈ range (n + 1), locallyNilpotentExpLinearMap f hf
          (algebraMap ℚ R (j.factorial : ℚ)⁻¹ • ((-f) ^ j) x)
      = ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), g (i, j) := by
        rw [sum_comm]
        refine sum_congr rfl fun j _ => ?_
        rw [neg_pow_apply, map_smul, map_smul]
        -- the linear map is the exponential series, which can be truncated at `n + 1`
        change _ • _ • locallyNilpotentExpFun f hf ((f ^ j) x) = _
        rw [locallyNilpotentExpFun_eq_sum f hf (hkill j), smul_sum, smul_sum]
        refine sum_congr rfl fun i _ => ?_
        simp only [g, smul_smul, ← Module.End.mul_apply, ← pow_add, map_mul, map_pow, map_neg,
          map_one]
        congr 1
        ring
    _ = ∑ m ∈ range (n + 1 + (n + 1)), ∑ ij ∈ antidiagonal m, g ij :=
        (TauCeti.sum_range_add_antidiagonal_of_support _ _ g hg).symm
    _ = ∑ m ∈ range (n + 1 + (n + 1)),
          (algebraMap ℚ R (if m = 0 then 1 else 0)) • (f ^ m) x := by
        refine sum_congr rfl fun m _ => ?_
        rw [← sum_antidiagonal_inv_factorial_mul_neg_one_pow m, map_sum, Finset.sum_smul]
        refine sum_congr rfl fun ij hij => ?_
        rw [mem_antidiagonal] at hij
        simp only [g, hij]
    _ = x := by
        rw [sum_eq_single_of_mem 0 (by simp) fun m _ hm => by simp [hm]]
        simp

/-- **The exponential of a locally nilpotent endomorphism.** If every vector is killed by some
power of `f`, then over a `ℚ`-algebra the exponential series `exp f x = ∑ fᵏ x / k!` is a finite
sum for each `x`, and it is a linear automorphism with inverse `exp (-f)`. No global nilpotence
bound is needed. -/
noncomputable def locallyNilpotentExp (f : Module.End R M) (hf : ∀ x, ∃ n, (f ^ n) x = 0) :
    M ≃ₗ[R] M :=
  have hf' : ∀ x, ∃ n, ((-f) ^ n) x = 0 := fun x =>
    (hf x).imp fun _ => neg_pow_apply_eq_zero f
  { locallyNilpotentExpLinearMap f hf with
    invFun := locallyNilpotentExpLinearMap (-f) hf'
    left_inv x := by
      have := locallyNilpotentExpLinearMap_neg_apply (-f) hf' (by simpa only [neg_neg] using hf) x
      simp only [neg_neg] at this
      exact this
    right_inv x := locallyNilpotentExpLinearMap_neg_apply f hf hf' x }

variable (f : Module.End R M) (hf : ∀ x, ∃ n, (f ^ n) x = 0)

/-- `exp f x` is its exponential series truncated at any power of `f` killing `x`. -/
theorem locallyNilpotentExp_apply_eq_sum {x : M} {n : ℕ} (hn : (f ^ n) x = 0) :
    locallyNilpotentExp f hf x =
      ∑ k ∈ range n, algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (f ^ k) x :=
  locallyNilpotentExpFun_eq_sum f hf hn

/-- The inverse of `exp f` is `exp (-f)`. -/
theorem symm_locallyNilpotentExp :
    (locallyNilpotentExp f hf).symm =
      locallyNilpotentExp (-f) fun x => (hf x).imp fun _ hn => by
        rw [neg_pow, Module.End.mul_apply, hn, map_zero] :=
  LinearEquiv.ext fun _ => (rfl)

/-- `exp f` fixes the vectors killed by `f`. -/
theorem locallyNilpotentExp_apply_of_apply_eq_zero {x : M} (hx : f x = 0) :
    locallyNilpotentExp f hf x = x := by
  rw [locallyNilpotentExp_apply_eq_sum f hf (n := 1) (by rwa [pow_one])]
  simp

/-- `exp f x = x + f x` when `f` kills `f x`. -/
theorem locallyNilpotentExp_apply_of_apply_apply_eq_zero {x : M} (hx : f (f x) = 0) :
    locallyNilpotentExp f hf x = x + f x := by
  rw [locallyNilpotentExp_apply_eq_sum f hf (n := 2) (by rwa [sq, Module.End.mul_apply])]
  simp [sum_range_succ]

/-- `exp f x = x + f x + y` when `f (f x) = 2 • y` and `f` kills `y`: the exponential series
stops after its quadratic term `f (f x) / 2`. -/
theorem locallyNilpotentExp_apply_of_apply_apply_eq_two_nsmul {x y : M}
    (hx : f (f x) = 2 • y) (hy : f y = 0) :
    locallyNilpotentExp f hf x = x + f x + y := by
  rw [locallyNilpotentExp_apply_eq_sum f hf (n := 3)
    (by rw [pow_succ, Module.End.mul_apply, sq, Module.End.mul_apply, hx, map_nsmul, hy,
      smul_zero])]
  simp only [sum_range_succ, range_zero, sum_empty, pow_zero, Module.End.one_apply, pow_one, sq,
    Module.End.mul_apply, hx, Nat.factorial, Nat.cast_one, inv_one, map_one, one_smul, zero_add]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, ← map_natCast (algebraMap ℚ R), ← map_mul]
  norm_num

end Module.End

end Exp
