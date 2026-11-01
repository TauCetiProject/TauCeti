/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Chevalley.Weyl
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Vector

/-!
# The Weyl automorphisms of the pinned Chevalley system

For a valid Dynkin type `t`, the named Chevalley system `e_γ = TauCeti.DynkinType.chevalleySystem`
of the pinned rational Lie algebra is indexed by the root numbers `Fin t.numRoots` of
`TauCeti.DynkinType.simplyConnectedRootDatum`. For a root `α`, the vectors `(α^∨, e_α, e_{-α})`
form an `sl₂` triple, whose Weyl automorphism

```text
w_α = exp (ad e_α) ∘ exp (ad (-e_{-α})) ∘ exp (ad e_α)
```

is the Lie-algebra form of Chevalley's element `n_α = x_α(1) x_{-α}(-1) x_α(1)`. This file proves,
in the root numbering, that it permutes the root vectors up to sign:

```text
w_α (e_β) = ± e_{s_α β},
```

and deduces that every root vector is reached from the simple root vectors `eᵢ` by the Weyl
automorphisms of the simple roots and signs. In a representation `w_α` is conjugation by `n_α`, so
these are the identities that express every root vector, and hence the root subgroup `x_γ` of every
root `γ` of the Chevalley group, through the simple ones: `e_γ = ± w e_{αᵢ}` for a composite `w` of
simple Weyl automorphisms.

## Main results

* `TauCeti.DynkinType.weylAut_chevalleySystem_eq_or_eq_neg`: `w_α (e_β) = ± e_{s_α β}`.
* `TauCeti.DynkinType.chevalleySystem_induction`: a property of the Lie algebra that is invariant
  under negation and under the Weyl automorphisms of the simple roots, and holds at the simple root
  vectors `eᵢ`, holds at every root vector `e_γ`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieAlgebra.IsKilling LieModule

variable (t : DynkinType) (ht : t.Valid)

/-- **The Weyl automorphisms permute the named root vectors up to sign.** For root numbers `α` and
`β`, the Weyl automorphism of the triple `(α^∨, e_α, e_{-α})` sends `e_β` to `e_{s_α β}` or to
`-e_{s_α β}`, where `s_α β` is the reflection of `β` in `α` in the pinned root datum. -/
theorem weylAut_chevalleySystem_eq_or_eq_neg (α β : Fin t.numRoots) :
    weylAut (t.isSl2Triple_chevalleySystem ht α) (t.isNilpotent_ad_chevalleySystem ht α)
          (t.isNilpotent_ad_chevalleySystem ht _) (t.chevalleySystem ht β) =
        t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm α β) ∨
      weylAut (t.isSl2Triple_chevalleySystem ht α) (t.isNilpotent_ad_chevalleySystem ht α)
          (t.isNilpotent_ad_chevalleySystem ht _) (t.chevalleySystem ht β) =
        -t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm α β) := by
  simpa only [← rootEquiv_reflectionPerm, extendRootFamily_rootEquiv,
    extendRootFamily_neg_rootEquiv] using
    (t.isChevalleySystem_chevalleySystem ht).weylAut_apply_eq_or_eq_neg (t.rootEquiv ht α)
      (t.rootEquiv ht β)

variable {t ht} in
/-- **Every root vector is reached from the simple ones by simple Weyl automorphisms.** A property
`p` of elements of the pinned Lie algebra that holds at the simple root vectors `eᵢ`, is invariant
under negation, and is preserved by the Weyl automorphism of the triple `(αᵢ^∨, eᵢ, fᵢ)` of every
simple root, holds at the root vector `e_γ` of every root `γ`. -/
theorem chevalleySystem_induction {p : t.lieAlgebra ht → Prop} (hneg : ∀ z, p z → p (-z))
    (hsimple : ∀ i, p ((t.lieBasis ht).e i))
    (hweyl : ∀ i z, p z → p (weylAut (t.isSl2Triple_chevalleySystem ht (t.simpleIndex ht i))
      (t.isNilpotent_ad_chevalleySystem ht _) (t.isNilpotent_ad_chevalleySystem ht _) z))
    (γ : Fin t.numRoots) : p (t.chevalleySystem ht γ) := by
  set P := t.simplyConnectedRootDatum ht
  -- a simple Weyl automorphism moves the root vector of `k` to that of `s_j k`, up to sign
  have step (i : Fin t.rank) (k : Fin t.numRoots) (hk : p (t.chevalleySystem ht k)) :
      p (t.chevalleySystem ht (P.reflectionPerm (t.simpleIndex ht i) k)) := by
    rcases t.weylAut_chevalleySystem_eq_or_eq_neg ht (t.simpleIndex ht i) k with h | h
    · exact h ▸ hweyl i _ hk
    · have := hneg _ (hweyl i _ hk)
      rwa [h, neg_neg] at this
  have hsupport {k : Fin t.numRoots} (hk : k ∈ (t.rationalBase ht).support) :
      ∃ i, k = t.simpleIndex ht i := by
    obtain ⟨i, hi⟩ := (t.simpleSupportEquiv ht).surjective ⟨k, hk⟩
    exact ⟨i, by rw [← coe_simpleSupportEquiv, hi]⟩
  -- induct on `γ` and `-γ` together: reflections in simple roots reach every root from the simple
  -- roots only once negation is available, and negation is not a simple Weyl automorphism
  refine ((t.rationalBase ht).induction_reflect γ
    (p := fun k => p (t.chevalleySystem ht k) ∧ p (t.chevalleySystem ht (P.reflectionPerm k k)))
    (fun k hk => ?_) (fun k hk => ?_) (fun k j hk hj => ?_)).1
  · have hkk : P.reflectionPerm (P.reflectionPerm k k) (P.reflectionPerm k k) = k :=
      ((P.root_eq_neg_iff).mp (by simp [P.root_reflectionPerm])).symm
    simp only [reflectionPerm_rationalRootSystem] at hk ⊢
    rw [hkk]
    exact hk.symm
  · obtain ⟨i, rfl⟩ := hsupport hk
    have hi : p (t.chevalleySystem ht (t.simpleIndex ht i)) := by simpa using hsimple i
    simpa only [reflectionPerm_rationalRootSystem] using ⟨hi, step i _ hi⟩
  · obtain ⟨i, rfl⟩ := hsupport hj
    have hneg_refl : P.reflectionPerm (t.simpleIndex ht i) (P.reflectionPerm k k) =
        P.reflectionPerm (P.reflectionPerm (t.simpleIndex ht i) k)
          (P.reflectionPerm (t.simpleIndex ht i) k) :=
      (P.root_eq_neg_iff).mp (by simp [P.root_reflectionPerm])
    simp only [reflectionPerm_rationalRootSystem] at hk ⊢
    exact ⟨step i k hk.1, hneg_refl ▸ step i _ hk.2⟩

end TauCeti.DynkinType
