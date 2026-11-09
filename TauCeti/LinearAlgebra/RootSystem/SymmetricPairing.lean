/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.RootString

/-!
# Root sums with symmetric integer pairings

For a root pairing over `ℤ` whose Cartan pairing is symmetric, a root sum `γ = α + β`
has pairing `⟨α, β^∨⟩ = -1`. Consequently `α + γ` is not a root.
No finiteness or spanning assumption is required.

## Main results

* `RootPairing.pairing_eq_neg_one_of_root_eq_add`: roots whose sum is a root pair to `-1`.
* `RootPairing.pairing_eq_one_of_root_eq_add`: a summand pairs to `1` with the root sum.
* `RootPairing.root_add_notMem_of_root_eq_add`: a root sum cannot be extended to another root.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §9.1.
-/

public section

namespace RootPairing

variable {ι M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
variable {P : RootPairing ι ℤ M N}
variable (hcomm : ∀ i j, P.pairing i j = P.pairing j i) {α β γ : ι}

include hcomm

/-- With symmetric integer pairings, roots whose sum is a root have Cartan pairing `-1`. -/
theorem pairing_eq_neg_one_of_root_eq_add (hγ : P.root γ = P.root α + P.root β) :
    P.pairing α β = -1 := by
  have hlen := P.length_of_root_eq_add_zsmul (fun _ ↦ 1)
    (by simpa only [one_mul] using fun i j ↦ hcomm j i) β α γ 1
    (by simpa only [one_zsmul] using hγ)
  norm_num at hlen
  omega

/-- With symmetric integer pairings, a summand pairs to `1` with the root sum `γ = α + β`. -/
theorem pairing_eq_one_of_root_eq_add (hγ : P.root γ = P.root α + P.root β) :
    P.pairing α γ = 1 := by
  have h₁ := pairing_eq_neg_one_of_root_eq_add hcomm hγ
  have h₂ := pairing_eq_add_of_root_eq_add (l := α) hγ
  rw [hcomm γ α, hcomm β α] at h₂
  simp only [pairing_same] at h₂
  omega

/-- With symmetric integer pairings, a root sum `γ = α + β` cannot be extended to `α + γ`. -/
theorem root_add_notMem_of_root_eq_add (hγ : P.root γ = P.root α + P.root β) :
    P.root α + P.root γ ∉ Set.range P.root := by
  rintro ⟨δ, hδ⟩
  have h₁ := pairing_eq_one_of_root_eq_add hcomm hγ
  have h₂ := pairing_eq_neg_one_of_root_eq_add hcomm hδ
  omega

end RootPairing
