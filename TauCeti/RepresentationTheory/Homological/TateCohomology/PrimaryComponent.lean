/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction
public import TauCeti.RepresentationTheory.Homological.TateCohomology.DimensionShift
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HomologySequence

/-!
# `p`-primary components of Tate cohomology

Let `G` be a finite group. Every Tate cohomology group `Ĥⁿ(G, A)`, in every integer degree `n`,
is killed by the order of `G` (`TauCeti.TateCohomology.natCard_nsmul_eq_zero`): in positive
degrees this is the restriction-corestriction argument through the trivial subgroup, and
dimension shifting moves it to every degree. Tate cohomology is a `k`-linear functor of the
coefficients, so a scalar acting bijectively on `A` acts bijectively on every `Ĥⁿ(G, A)`
(`TauCeti.TateCohomology.bijective_smul_tateCohomology`).

Together these say that `p`-primary Tate cohomology sees only `p`: if multiplication by `p` is
bijective on `A`, the `p`-primary component of `Ĥⁿ(S, A)` vanishes for every subgroup `S` and
every `n` (`TauCeti.TateCohomology.primaryComponent_tateCohomology_eq_bot`). Since Tate cohomology
is torsion, a `p`-primary class in the image of a map of Tate cohomology groups has a `p`-primary
preimage (`TauCeti.exists_mem_primaryComponent_apply_eq`), so the long exact sequence of a short
exact sequence `0 → X₁ → X₂ → X₃ → 0` stays exact on `p`-primary components. Hence, for a prime
`p`, if multiplication by `p` is bijective on `X₃` the map `Ĥⁿ(G, X₁) → Ĥⁿ(G, X₂)` is a bijection
of `p`-primary components, and if it is bijective on `X₁` so is `Ĥⁿ(G, X₂) → Ĥⁿ(G, X₃)`, in every
degree. Applied to the two short exact sequences through the image of a morphism whose kernel
and cokernel have bijective multiplication by `p`, they show that such a morphism induces
bijections on the `p`-primary components of Tate cohomology, as for the map from the
multiplicative group of a `p`-adic field to its `p`-adic completion.

## Main statements

* `TauCeti.TateCohomology.natCard_nsmul_eq_zero`: `#G` kills `Ĥⁿ(G, A)` for every `n : ℤ`.
* `TauCeti.TateCohomology.isAddTorsion_tateCohomology`: `Ĥⁿ(G, A)` is a torsion group.
* `TauCeti.TateCohomology.bijective_smul_tateCohomology`: a scalar acting bijectively on `A` acts
  bijectively on `Ĥⁿ(G, A)`.
* `TauCeti.TateCohomology.primaryComponent_tateCohomology_eq_bot`: if multiplication by `p` is
  bijective on `A`, the `p`-primary component of `Ĥⁿ(S, A)` is trivial.
* `TauCeti.TateCohomology.map_f_bijOn_primaryComponent`,
  `TauCeti.TateCohomology.map_g_bijOn_primaryComponent`: the two maps of a short exact sequence
  on the `p`-primary components of Tate cohomology.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5 (`#G` kills Tate cohomology).
-/

public section

universe u

open CategoryTheory Limits

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- After `d` downward dimension shifts every degree `n` with `1 ≤ n + d` is positive, where the
cohomology of a finite group is killed by its order. -/
private theorem natCard_nsmul_eq_zero_aux (d : ℕ) (A : Rep k G) (n : ℤ) (hn : 1 ≤ n + d)
    (x : tateCohomology A n) : Nat.card G • x = 0 := by
  induction d generalizing A n with
  | zero =>
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m + 1 : ℕ) := ⟨(n - 1).toNat, by omega⟩
    let e := ((_root_.TateCohomology.isoGroupCohomology (m + 1)).app A).toLinearEquiv
    exact e.injective (by rw [map_nsmul, map_zero]; exact groupCohomology.natCard_nsmul_eq_zero _)
  | succ d ih =>
    let e := (dimensionShiftDownIso A n).toLinearEquiv
    exact e.injective (by
      rw [map_nsmul, map_zero]
      exact ih (Rep.dimensionShiftDown A) (n + 1) (by push_cast at hn; omega) _)

/-- **Tate cohomology of a finite group is killed by the order of the group**, in every integer
degree. -/
theorem natCard_nsmul_eq_zero {A : Rep k G} {n : ℤ} (x : tateCohomology A n) :
    Nat.card G • x = 0 :=
  natCard_nsmul_eq_zero_aux (1 - n).toNat A n (by omega) x

/-- Tate cohomology of a finite group is a torsion group. -/
theorem isAddTorsion_tateCohomology (A : Rep k G) (n : ℤ) :
    IsAddTorsion (tateCohomology A n) := fun x ↦
  isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨Nat.card G, Nat.card_pos, natCard_nsmul_eq_zero x⟩

/-- If a scalar `c` acts bijectively on `A`, it acts bijectively on every Tate cohomology group
of `A`. -/
theorem bijective_smul_tateCohomology {A : Rep k G} {c : k}
    (hc : Function.Bijective fun a : A.V ↦ c • a) (n : ℤ) :
    Function.Bijective fun x : tateCohomology A n ↦ c • x := by
  -- `c • 𝟙 A` is an isomorphism, and Tate cohomology is a `k`-linear functor.
  have : IsIso (c • 𝟙 A) := by
    have : IsIso ((forget (Rep k G)).map (c • 𝟙 A)) := (isIso_iff_bijective _).2 hc
    exact isIso_of_reflects_iso _ (forget (Rep k G))
  have h := ConcreteCategory.bijective_of_isIso ((tateCohomologyFunctor n).map (c • 𝟙 A))
  rw [Functor.map_smul, CategoryTheory.Functor.map_id] at h
  -- The morphism `c • 𝟙` of `ModuleCat k` is, as a function, `x ↦ c • x`.
  exact h

/-- If multiplication by `p` is bijective on `A`, the `p`-primary component of `Ĥⁿ(G, A)` is
trivial. -/
private theorem primaryComponent_eq_bot_of_bijective {p : ℕ} {A : Rep k G}
    (hA : Function.Bijective fun a : A.V ↦ (p : k) • a) (n : ℤ) :
    AddCommGroup.primaryComponent (tateCohomology A n) p = ⊥ :=
  primaryComponent_eq_bot_of_injective_nsmul <| by
    simpa only [Nat.cast_smul_eq_nsmul] using (bijective_smul_tateCohomology hA n).injective

omit [Fintype G] in
/-- **`p`-primary Tate cohomology sees only `p`.** If multiplication by `p` is bijective on `A`,
the `p`-primary component of `Ĥⁿ(S, A)` is trivial for every subgroup `S` of `G` and every
integer `n`. -/
theorem primaryComponent_tateCohomology_eq_bot (p : ℕ) (A : Rep k G)
    (hA : Function.Bijective fun a : A.V ↦ (p : k) • a) (S : Subgroup G) [Fintype S] (n : ℤ) :
    AddCommGroup.primaryComponent (tateCohomology (Rep.res S.subtype A) n) p = ⊥ :=
  primaryComponent_eq_bot_of_bijective (A := Rep.res S.subtype A) hA n

section ShortExact

variable {S : ShortComplex (Rep k G)} (hS : S.ShortExact) {p : ℕ} (hp : p.Prime)
include hS hp

/-- **The first map of a short exact sequence on `p`-primary Tate cohomology.** For a short exact
sequence `0 → X₁ → X₂ → X₃ → 0` and a prime `p` such that multiplication by `p` is bijective on
`X₃`, the map `Ĥⁿ(G, X₁) → Ĥⁿ(G, X₂)` restricts to a bijection of `p`-primary components. -/
theorem map_f_bijOn_primaryComponent (h₃ : Function.Bijective fun x : S.X₃.V ↦ (p : k) • x)
    (n : ℤ) :
    Set.BijOn ((tateCohomologyFunctor n).map S.f)
      (AddCommGroup.primaryComponent (tateCohomology S.X₁ n) p)
      (AddCommGroup.primaryComponent (tateCohomology S.X₂ n) p) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by ring⟩
  refine ⟨fun x ⟨j, hj⟩ ↦ ⟨j, by rw [← map_nsmul, hj, map_zero]⟩, ?_, fun z hz ↦ ?_⟩
  · refine fun x hx y hy hxy ↦ sub_eq_zero.1 ?_
    have hxy' : (tateCohomologyFunctor (m + 1)).map S.f (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    -- `x - y` is the image under `δ` of a class of `Ĥᵐ(G, X₃)`, which may be taken `p`-primary.
    obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (_root_.TateCohomology.exact₁ hS m) _ hxy'
    obtain ⟨w', hw', hww'⟩ := exists_mem_primaryComponent_apply_eq
      (_root_.TateCohomology.δ hS m).hom hp (isAddTorsion_tateCohomology _ _ w)
      (hw ▸ sub_mem hx hy)
    rw [primaryComponent_eq_bot_of_bijective h₃, AddSubgroup.mem_bot] at hw'
    rw [← hw, ← hww', hw', map_zero]
  · -- The image of `z` in `Ĥᵐ⁺¹(G, X₃)` is `p`-primary, hence zero, so `z` comes from `X₁`.
    have hgz : (tateCohomologyFunctor (m + 1)).map S.g z = 0 := by
      obtain ⟨j, hj⟩ := hz
      have hmem : (tateCohomologyFunctor (m + 1)).map S.g z ∈
          AddCommGroup.primaryComponent _ p := ⟨j, by rw [← map_nsmul, hj, map_zero]⟩
      rwa [primaryComponent_eq_bot_of_bijective h₃, AddSubgroup.mem_bot] at hmem
    obtain ⟨x, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (_root_.TateCohomology.exact₂ hS (m + 1)) z hgz
    obtain ⟨x', hx', hxx'⟩ := exists_mem_primaryComponent_apply_eq
      ((tateCohomologyFunctor (m + 1)).map S.f).hom hp (isAddTorsion_tateCohomology _ _ x) hz
    exact ⟨x', hx', hxx'⟩

/-- **The second map of a short exact sequence on `p`-primary Tate cohomology.** For a short
exact sequence `0 → X₁ → X₂ → X₃ → 0` and a prime `p` such that multiplication by `p` is
bijective on `X₁`, the map `Ĥⁿ(G, X₂) → Ĥⁿ(G, X₃)` restricts to a bijection of `p`-primary
components. -/
theorem map_g_bijOn_primaryComponent (h₁ : Function.Bijective fun x : S.X₁.V ↦ (p : k) • x)
    (n : ℤ) :
    Set.BijOn ((tateCohomologyFunctor n).map S.g)
      (AddCommGroup.primaryComponent (tateCohomology S.X₂ n) p)
      (AddCommGroup.primaryComponent (tateCohomology S.X₃ n) p) := by
  refine ⟨fun x ⟨j, hj⟩ ↦ ⟨j, by rw [← map_nsmul, hj, map_zero]⟩, ?_, fun w hw ↦ ?_⟩
  · refine fun x hx y hy hxy ↦ sub_eq_zero.1 ?_
    have hxy' : (tateCohomologyFunctor n).map S.g (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    -- `x - y` comes from `Ĥⁿ(G, X₁)`, from a class which may be taken `p`-primary.
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (_root_.TateCohomology.exact₂ hS n) _ hxy'
    obtain ⟨z', hz', hzz'⟩ := exists_mem_primaryComponent_apply_eq
      ((tateCohomologyFunctor n).map S.f).hom hp (isAddTorsion_tateCohomology _ _ z)
      (hz ▸ sub_mem hx hy)
    rw [primaryComponent_eq_bot_of_bijective h₁, AddSubgroup.mem_bot] at hz'
    rw [← hz, ← hzz', hz', map_zero]
  · -- The image of `w` under `δ` is `p`-primary in `Ĥⁿ⁺¹(G, X₁)`, hence zero, so `w` comes from
    -- `X₂`.
    have hδw : _root_.TateCohomology.δ hS n w = 0 := by
      obtain ⟨j, hj⟩ := hw
      have hmem : _root_.TateCohomology.δ hS n w ∈ AddCommGroup.primaryComponent _ p :=
        ⟨j, by rw [← map_nsmul, hj, map_zero]⟩
      rwa [primaryComponent_eq_bot_of_bijective h₁, AddSubgroup.mem_bot] at hmem
    obtain ⟨z, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (_root_.TateCohomology.exact₃ hS n) w hδw
    obtain ⟨z', hz', hzz'⟩ := exists_mem_primaryComponent_apply_eq
      ((tateCohomologyFunctor n).map S.g).hom hp (isAddTorsion_tateCohomology _ _ z) hw
    exact ⟨z', hz', hzz'⟩

end ShortExact

end TauCeti.TateCohomology
