/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Basis
public import TauCeti.Algebra.Lie.Weights.Chevalley.Weyl
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Vector
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

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

## Main definitions

* `TauCeti.DynkinType.chevalleyWeylSign`: the sign `ε` with `w_α e_β = ε e_{s_α β}`.

## Main results

* `TauCeti.DynkinType.weylAut_chevalleySystem_eq_or_eq_neg`: `w_α (e_β) = ± e_{s_α β}`.
* `TauCeti.DynkinType.weylAut_chevalleySystem`: `w_α e_β = ε e_{s_α β}` with the sign
  `ε = TauCeti.DynkinType.chevalleyWeylSign α β`.
* `TauCeti.DynkinType.weylAut_simpleIndex_eq`: at a simple root `αᵢ`, `w_{αᵢ}` is the Weyl
  automorphism of any `sl₂` triple `(h, eᵢ, fᵢ)` on its numbered generators, such as the basis
  triple `LieAlgebra.Basis.isSl2Triple_rootGenerator`.
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
    weylAut (t.isSl2Triple_chevalleySystem ht α)
          (t.isNilpotent_ad_chevalleySystem ht α).exists_pow_apply_eq_zero
          (t.isNilpotent_ad_chevalleySystem ht _).exists_pow_apply_eq_zero
          (t.chevalleySystem ht β) =
        t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm α β) ∨
      weylAut (t.isSl2Triple_chevalleySystem ht α)
          (t.isNilpotent_ad_chevalleySystem ht α).exists_pow_apply_eq_zero
          (t.isNilpotent_ad_chevalleySystem ht _).exists_pow_apply_eq_zero
          (t.chevalleySystem ht β) =
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
      (t.isNilpotent_ad_chevalleySystem ht _).exists_pow_apply_eq_zero
      (t.isNilpotent_ad_chevalleySystem ht _).exists_pow_apply_eq_zero z))
    (γ : Fin t.numRoots) : p (t.chevalleySystem ht γ) := by
  -- a simple Weyl automorphism moves the root vector of `k` to that of `s_j k`, up to sign
  have step (i : Fin t.rank) (k : Fin t.numRoots) (hk : p (t.chevalleySystem ht k)) :
      p (t.chevalleySystem ht
        ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) k)) := by
    rcases t.weylAut_chevalleySystem_eq_or_eq_neg ht (t.simpleIndex ht i) k with h | h
    · exact h ▸ hweyl i _ hk
    · have := hneg _ (hweyl i _ hk)
      rwa [h, neg_neg] at this
  refine (t.rationalBase ht).induction_simple_reflect γ (p := fun k => p (t.chevalleySystem ht k))
    (fun k hk => ?_) (fun k j hk hj => ?_)
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hk
    simpa using hsimple i
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hj
    simpa only [reflectionPerm_rationalRootSystem] using step i k hk

/-! ## The sign of a Weyl automorphism on a root vector -/

noncomputable section

/-- **The sign of a Weyl automorphism on a root vector**: the unit `ε = ±1` with
`w_α e_β = ε e_{s_α β}`, where `w_α` is the Weyl automorphism of the `sl₂` triple
`(α^∨, e_α, e_{-α})` of the named Chevalley system and `s_α β` is the reflection of `β` in `α`
(Carter's `η_{α,β}`). That it is such a sign is `TauCeti.DynkinType.weylAut_chevalleySystem`. -/
def chevalleyWeylSign (α β : Fin t.numRoots) : ℤˣ :=
  open Classical in
  if weylAut (t.isSl2Triple_chevalleySystem ht α) (t.isNilpotent_ad_chevalleySystem ht α)
      (t.isNilpotent_ad_chevalleySystem ht _) (t.chevalleySystem ht β) =
      t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm α β) then 1 else -1

end

/-- **The Weyl automorphisms permute the named root vectors with a sign.** The Weyl automorphism
of the triple `(α^∨, e_α, e_{-α})` sends `e_β` to `ε e_{s_α β}` for `ε = chevalleyWeylSign α β`. -/
theorem weylAut_chevalleySystem (α β : Fin t.numRoots) :
    weylAut (t.isSl2Triple_chevalleySystem ht α) (t.isNilpotent_ad_chevalleySystem ht α)
        (t.isNilpotent_ad_chevalleySystem ht _) (t.chevalleySystem ht β) =
      (t.chevalleyWeylSign ht α β : ℤ) •
        t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm α β) := by
  rw [chevalleyWeylSign]
  split_ifs with h
  · rw [h, Units.val_one, one_zsmul]
  · rw [(t.weylAut_chevalleySystem_eq_or_eq_neg ht α β).resolve_left h, Units.val_neg,
      Units.val_one, neg_one_zsmul]

variable {t ht} in
/-- The sign `chevalleyWeylSign α β` is the only unit `ε` with `w_α e_β = ε e_{s_α β}`, since the
root vector `e_{s_α β}` is nonzero. -/
theorem eq_chevalleyWeylSign_iff {α β : Fin t.numRoots} {ε : ℤˣ} :
    ε = t.chevalleyWeylSign ht α β ↔
      weylAut (t.isSl2Triple_chevalleySystem ht α) (t.isNilpotent_ad_chevalleySystem ht α)
          (t.isNilpotent_ad_chevalleySystem ht _) (t.chevalleySystem ht β) =
        (ε : ℤ) • t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm α β) := by
  refine ⟨fun h => h ▸ t.weylAut_chevalleySystem ht α β, fun h => ?_⟩
  rw [t.weylAut_chevalleySystem ht α β, ← sub_eq_zero, ← sub_smul, ← Int.cast_smul_eq_zsmul ℚ,
    smul_eq_zero, Int.cast_eq_zero, sub_eq_zero, Units.val_inj] at h
  exact (h.resolve_right (t.isSl2Triple_chevalleySystem ht _).e_ne_zero).symm

/-! ## The Weyl automorphisms of the simple roots -/

section Simple

variable {t ht}

/-- **The Weyl automorphism of a simple root, read off its numbered generators**: the triple of the
simple root `αᵢ` in the named Chevalley system is `(αᵢ^∨, eᵢ, fᵢ)`, and the Weyl automorphism
depends only on its raising and lowering elements. -/
theorem weylAut_simpleIndex_eq (i : Fin t.rank) {h₀ : t.lieAlgebra ht}
    (T : IsSl2Triple h₀ ((t.lieBasis ht).rootGenerator (.inl i))
      ((t.lieBasis ht).rootGenerator (.inr i)))
    (he : IsNilpotent (ad ℚ (t.lieAlgebra ht) ((t.lieBasis ht).rootGenerator (.inl i))))
    (hf : IsNilpotent (ad ℚ (t.lieAlgebra ht) ((t.lieBasis ht).rootGenerator (.inr i)))) :
    weylAut (t.isSl2Triple_chevalleySystem ht (t.simpleIndex ht i))
        (t.isNilpotent_ad_chevalleySystem ht _) (t.isNilpotent_ad_chevalleySystem ht _) =
      weylAut T he hf := by
  have key : ∀ (a b : t.lieAlgebra ht) (_ : a = (t.lieBasis ht).rootGenerator (.inl i))
      (_ : b = (t.lieBasis ht).rootGenerator (.inr i)) {h₁ : t.lieAlgebra ht}
      (T' : IsSl2Triple h₁ a b)
      (ha : IsNilpotent (ad ℚ (t.lieAlgebra ht) a)) (hb : IsNilpotent (ad ℚ (t.lieAlgebra ht) b)),
      weylAut T' ha hb = weylAut T he hf := by
    rintro a b rfl rfl h₁ T' ha hb
    ext y
    rw [weylAut_apply ha hb, weylAut_apply he hf]
  exact key _ _ ((t.chevalleySystem_simpleIndex ht i).trans (Basis.rootGenerator_inl _ i).symm)
    ((t.chevalleySystem_reflectionPerm_simpleIndex ht i).trans (Basis.rootGenerator_inr _ i).symm)
    _ _ _

/-- The simple raising generator `eᵢ` is ad-nilpotent. -/
theorem isNilpotent_ad_rootGenerator_inl (i : Fin t.rank) :
    IsNilpotent (ad ℚ (t.lieAlgebra ht) ((t.lieBasis ht).rootGenerator (.inl i))) := by
  simpa using t.isNilpotent_ad_chevalleySystem ht (t.simpleIndex ht i)

/-- The simple lowering generator `fᵢ` is ad-nilpotent. -/
theorem isNilpotent_ad_rootGenerator_inr (i : Fin t.rank) :
    IsNilpotent (ad ℚ (t.lieAlgebra ht) ((t.lieBasis ht).rootGenerator (.inr i))) := by
  simpa using t.isNilpotent_ad_chevalleySystem ht
    ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i))

end Simple

end TauCeti.DynkinType
