/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
import TauCeti.RingTheory.Depth.WeaklyRegular

/-!
# Vanishing below the depth, axiomatically

Let `A` be a commutative ring and `M ↦ Hⁿ(M)` a family of maps from `A`-modules to `A`-modules,
indexed by `n : ℕ`, with two properties:

* *torsion*: every element of every `Hⁿ(N)` is killed by a power of each element `r` of some
  ideal `I` (or of a given sequence);
* *regularity*: if `r` is regular on `N` and `Hᵐ(N ⧸ r N) = 0` for every `m < n`, then `r` is
  regular on `Hⁿ(N)`.

Then `Hⁿ(M) = 0` as soon as `I` contains a weakly `M`-regular sequence of length greater than
`n`. The proof is an induction on `n` that uses the elements of the sequence one after the other:
if `rs = r :: rs'`, then `rs'` is weakly regular on `M ⧸ r M`, so `Hᵐ(M ⧸ r M) = 0` for `m < n`
by induction, hence `r` is regular on `Hⁿ(M)`; as every element of `Hⁿ(M)` is killed by a power
of `r`, `Hⁿ(M) = 0`.

No functoriality, exactness, finiteness or Noetherian hypothesis is needed. The families `H` of
interest are the groups `Extⁿ(A ⧸ I, −)` and the local cohomology groups `Hⁿ_I(−)` (for the
latter, over a Noetherian ring, Tau Ceti has `localCohomology.isZero_obj_of_lt_depth`), and
relative cohomology groups of functors on rings, computed through modules over `A`, for which no
long exact sequence in the module variable is available a priori. Over a Noetherian ring and for a
finite module, the existence of the regular sequence follows from a bound on the depth
`Ideal.depth`, through `Ideal.exists_isWeaklyRegular_of_le_depth`; this gives the vanishing below
the depth.

## Main results

* `RingTheory.Sequence.IsWeaklyRegular.subsingleton_of_lt_length`: if `rs` is weakly `M`-regular
  and longer than `n`, and the two properties hold for the elements of `rs`, then `Hⁿ(M) = 0`.
* `Ideal.subsingleton_of_isWeaklyRegular`: the same with the properties stated for the elements
  of an ideal `I` containing the sequence.
* `Ideal.subsingleton_of_lt_depth`: over a Noetherian ring, `Hⁿ(M) = 0` for a finite module `M`
  and every `n < I.depth M`.

## References

* This result corresponds to `New.Variety.depth_vanishing` and
  `New.Variety.DepthVanishing.subsingleton_of_isWeaklyRegular` in the file
  `Lib/Cohomology/Hodge/DepthVanishing` of the folder `grh` of https://github.com/lsernau/grh-lean
  at commit 72fead102f663d5c7a407964a13dc0cf9d977207, whose route (induction on `n`, using the
  elements of the regular sequence one after the other) is followed here. In the statements
  here, the regularity hypothesis is required only for the elements of `I` (resp. of the
  sequence), not for every element regular on `N`, and so is the torsion hypothesis in the
  sequence form.
* For the classical case `H = Ext(A ⧸ I, −)`: H. Matsumura, *Commutative Ring Theory*, Theorem 16.6;
  for local cohomology: [Stacks Project, Lemma 47.11.1](https://stacks.math.columbia.edu/tag/0AVZ).
-/

public section

universe w v u

open CategoryTheory

variable {A : Type u} [CommRing A]

namespace RingTheory.Sequence.IsWeaklyRegular

/-- **Depth vanishing**, axiomatic form. Let `H : ℕ → ModuleCat A → ModuleCat A` be a family of
maps such that, for each element `r` of a list `rs`, every element of every `Hⁿ(N)` is killed by a
power of `r`, and `r` is regular on `Hⁿ(N)` whenever `r` is regular on `N` and `Hᵐ(N ⧸ r N) = 0`
for all `m < n`. If `rs` is weakly regular on `M` and has length greater than `n`, then
`Hⁿ(M) = 0`. -/
theorem subsingleton_of_lt_length (H : ℕ → ModuleCat.{v} A → ModuleCat.{w} A) {rs : List A}
    (htors : ∀ r ∈ rs, ∀ n N (x : H n N), ∃ k : ℕ, r ^ k • x = 0)
    (hreg : ∀ r ∈ rs, ∀ n (N : ModuleCat.{v} A), IsSMulRegular N r →
      (∀ m < n, Subsingleton (H m (.of A (QuotSMulTop r N)))) → IsSMulRegular (H n N) r)
    {M : ModuleCat.{v} A} (hrs : IsWeaklyRegular M rs) {n : ℕ} (hn : n < rs.length) :
    Subsingleton (H n M) := by
  induction n using Nat.strong_induction_on generalizing M rs with
  | _ n ih =>
  obtain _ | ⟨r, rs⟩ := rs
  · simp at hn
  have hrs' := (isWeaklyRegular_cons_iff M r rs).1 hrs
  -- The tail is weakly regular on `M ⧸ r M`, so the lower groups of `M ⧸ r M` vanish.
  have hlow (m : ℕ) (hm : m < n) : Subsingleton (H m (.of A (QuotSMulTop r M))) :=
    ih m hm (fun s hs ↦ htors s (List.mem_cons_of_mem r hs))
      (fun s hs ↦ hreg s (List.mem_cons_of_mem r hs)) hrs'.2
      (by simp only [List.length_cons] at hn; omega)
  have hr := hreg r List.mem_cons_self n M hrs'.1 hlow
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨k, hk⟩ := htors r List.mem_cons_self n M x
  exact (hr.pow k).right_eq_zero_of_smul hk

end RingTheory.Sequence.IsWeaklyRegular

namespace Ideal

open RingTheory.Sequence

/-- **Depth vanishing.** Let `I` be an ideal and `H : ℕ → ModuleCat A → ModuleCat A` a family of
maps such that every element of every `Hⁿ(N)` is killed by a power of each element of `I`, and an
element `r ∈ I` regular on `N` is regular on `Hⁿ(N)` whenever `Hᵐ(N ⧸ r N) = 0` for all `m < n`.
If `I` contains a weakly `M`-regular sequence of length greater than `n`, then `Hⁿ(M) = 0`. -/
theorem subsingleton_of_isWeaklyRegular (I : Ideal A) (H : ℕ → ModuleCat.{v} A → ModuleCat.{w} A)
    (htors : ∀ r ∈ I, ∀ n N (x : H n N), ∃ k : ℕ, r ^ k • x = 0)
    (hreg : ∀ r ∈ I, ∀ n (N : ModuleCat.{v} A), IsSMulRegular N r →
      (∀ m < n, Subsingleton (H m (.of A (QuotSMulTop r N)))) → IsSMulRegular (H n N) r)
    {M : ModuleCat.{v} A} {rs : List A} (hI : ∀ r ∈ rs, r ∈ I) (hrs : IsWeaklyRegular M rs)
    {n : ℕ} (hn : n < rs.length) :
    Subsingleton (H n M) :=
  hrs.subsingleton_of_lt_length H (fun r hr ↦ htors r (hI r hr)) (fun r hr ↦ hreg r (hI r hr)) hn

/-- **Vanishing below the depth.** Let `M` be a finite module over a Noetherian ring, `I` an
ideal, and `H : ℕ → ModuleCat A → ModuleCat A` a family of maps such that every element of every
`Hⁿ(N)` is killed by a power of each element of `I`, and an element `r ∈ I` regular on `N` is
regular on `Hⁿ(N)` whenever `Hᵐ(N ⧸ r N) = 0` for all `m < n`. Then `Hⁿ(M) = 0` for every
`n < I.depth M`; in particular `Hⁿ(M) = 0` for all `n` when `I M = M`. For a local ring and its
maximal ideal, `I.depth M` is `IsLocalRing.depth M`. -/
theorem subsingleton_of_lt_depth [IsNoetherianRing A] [Small.{v} A] (I : Ideal A)
    (H : ℕ → ModuleCat.{v} A → ModuleCat.{w} A)
    (htors : ∀ r ∈ I, ∀ n N (x : H n N), ∃ k : ℕ, r ^ k • x = 0)
    (hreg : ∀ r ∈ I, ∀ n (N : ModuleCat.{v} A), IsSMulRegular N r →
      (∀ m < n, Subsingleton (H m (.of A (QuotSMulTop r N)))) → IsSMulRegular (H n N) r)
    (M : ModuleCat.{v} A) [Module.Finite A M] {n : ℕ} (hn : (n : ℕ∞) < I.depth M) :
    Subsingleton (H n M) := by
  obtain ⟨rs, hlen, hI, hrs⟩ := I.exists_isWeaklyRegular_of_le_depth M (n := n + 1)
    (by exact_mod_cast Order.add_one_le_of_lt hn)
  exact I.subsingleton_of_isWeaklyRegular H htors hreg hI hrs (by omega)

end Ideal
