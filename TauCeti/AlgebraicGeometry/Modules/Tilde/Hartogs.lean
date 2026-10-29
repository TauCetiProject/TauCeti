/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Extending sections of `M~` across a closed subset of depth at least two

Let `M` be a module over a commutative ring `R` and `U` an open subset of `Spec R`. If `a, b` is a
weakly `M`-regular sequence whose basic opens `D(a)` and `D(b)` lie in `U`, then every section of
`M~` over `U` comes from a unique element of `M`: the map `M → M~(U)` is bijective. This is the
algebraic Hartogs principle for `M~` on the affine scheme `Spec R`.

For a finite module `M` over a Noetherian ring, the hypothesis is implied by a condition at the
points outside `U`: if `depth M_p ≥ 2` for every prime `p ∉ U`, the vanishing ideal of the
complement of `U` contains a weakly `M`-regular sequence of length two
(`TauCeti.exists_isWeaklyRegular_of_le_depth_localizedModule`). So sections of `M~` extend
uniquely across a closed subset all of whose points have depth at least two (Stacks, Lemma 31.5.11
(0E9I), for the affine scheme `Spec R` and the quasi-coherent sheaf `M~`). For instance, for
`M = R = k[x, y]` it gives `Γ(𝔸² ∖ {0}, 𝒪) = k[x, y]`, since `k[x, y]_{(x, y)}` has depth two.

The proof is elementary. A section `s` over `U` restricts to fractions `x / aⁿ` on `D(a)` and
`y / bᵐ` on `D(b)`. Their agreement on `D(ab)` gives `bʲ x ∈ aⁿ M` for some `j`, so `x = aⁿ c`
because `b` is regular modulo `a`. Then `s` and `c` agree on `D(a)`, and since `a` is `M`-regular, a
section over `U` is determined by its restriction to `U ∩ D(a)`.

## Main results

* `TauCeti.AlgebraicGeometry.StructureSheaf.res_injective_of_isSMulRegular`: for an `M`-regular
  element `a`, a section of `M~` over `U` is determined by its restriction to any open `V ⊆ U`
  containing `U ∩ D(a)`.
* `TauCeti.AlgebraicGeometry.StructureSheaf.toOpenₗ_injective_of_isSMulRegular`: `M → M~(U)` is
  injective when `D(a) ⊆ U` for an `M`-regular `a`.
* `TauCeti.AlgebraicGeometry.StructureSheaf.toOpenₗ_bijective_of_isWeaklyRegular`: `M → M~(U)` is
  bijective when `D(a), D(b) ⊆ U` for a weakly `M`-regular sequence `a, b`.
* `TauCeti.AlgebraicGeometry.tilde_toOpen_bijective_of_two_le_depth`: for a finite module over a
  Noetherian ring, `M → M~(U)` is bijective when `depth M_p ≥ 2` at every prime `p ∉ U`.

## References

* [Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I).
-/

public section

universe u

open CategoryTheory Opposite TopologicalSpace IsLocalRing RingTheory.Sequence Pointwise
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.StructureSheaf
open PrimeSpectrum (basicOpen)

namespace TauCeti.AlgebraicGeometry

namespace StructureSheaf

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- Let `a` be `M`-regular. A section of `M~` over `U` vanishing at every point of `U ∩ D(a)`
vanishes. -/
private lemma eq_zero_of_isSMulRegular {U : Opens (PrimeSpectrum.Top R)} {a : R}
    (ha : IsSMulRegular M a) (s : (structureSheafInType R M).1.obj (op U))
    (hs : ∀ x : U, x.1 ∈ basicOpen a → s.1 x = 0) : s = 0 := by
  refine Subtype.ext (funext fun x ↦ ?_)
  -- Near `x`, the section `s` is a fraction `z / g`.
  obtain ⟨g, hxg, i, z, hz⟩ := exists_const U s x.1 x.2
  have hval (y : PrimeSpectrum.Top R) (hy : y ∈ basicOpen g) :
      s.1 ⟨y, i hy⟩ = LocalizedModule.mk z ⟨g, hy⟩ :=
    (congrArg (fun t ↦ t.1 ⟨y, hy⟩) hz).symm
  -- The fraction `z / g` vanishes on `D(g a)`, so `(g a)ᵏ z = 0`, hence `gᵏ z = 0`.
  have hzero : toOpenₗ R M (basicOpen (g * a)) z = 0 := by
    refine Subtype.ext (funext fun y ↦ ?_)
    obtain ⟨hyg, hya⟩ : y.1 ∈ basicOpen g ∧ y.1 ∈ basicOpen a := by
      simpa [PrimeSpectrum.basicOpen_mul] using y.2
    have hy0 := (hval y.1 hyg).symm.trans (hs ⟨y.1, i hyg⟩ hya)
    rw [← LocalizedModule.zero_mk ⟨g, hyg⟩, LocalizedModule.mk_eq] at hy0
    obtain ⟨u, hu⟩ := hy0
    -- A section of `M~` is a family of fractions, and `toOpenₗ` sends `z` to the family `z / 1`;
    -- `change` evaluates both sides at `y`.
    change LocalizedModule.mk z 1 = 0
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
    exact ⟨u * ⟨g, hyg⟩, by simpa [mul_smul] using hu⟩
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalizedModule.eq_zero_iff (.powers (g * a))
    (toOpenₗ R M (basicOpen (g * a)))).1 hzero
  have hgk : g ^ k • z = 0 :=
    (ha.pow k).right_eq_zero_of_smul (by rw [smul_smul, ← mul_pow, mul_comm]; exact hk)
  rw [hval x.1 hxg]
  refine (LocalizedModule.mk_eq.2 ⟨⟨g ^ k, x.1.asIdeal.primeCompl.pow_mem hxg k⟩, ?_⟩).trans
    (LocalizedModule.zero_mk 1)
  simp [hgk]

/-- Let `a` be `M`-regular and `V ⊆ U` opens of `Spec R` with `U ∩ D(a) ⊆ V`. A section of `M~`
over `U` is determined by its restriction to `V`. -/
theorem res_injective_of_isSMulRegular {U V : Opens (PrimeSpectrum.Top R)} (hVU : V ≤ U) {a : R}
    (ha : IsSMulRegular M a) (haV : U ⊓ basicOpen a ≤ V) :
    Function.Injective ((structureSheafInType R M).1.map (homOfLE hVU).op) := by
  intro s t hst
  rw [← sub_eq_zero]
  refine eq_zero_of_isSMulRegular ha (s - t) fun x hx ↦ ?_
  have := congrArg (fun r ↦ r.1 ⟨x.1, haV ⟨x.2, hx⟩⟩) hst
  exact sub_eq_zero.2 this

/-- Let `a` be `M`-regular. If `D(a) ⊆ U`, then `M → M~(U)` is injective. -/
theorem toOpenₗ_injective_of_isSMulRegular {U : Opens (PrimeSpectrum.Top R)} {a : R}
    (ha : IsSMulRegular M a) (haU : basicOpen a ≤ U) : Function.Injective (toOpenₗ R M U) := by
  refine (injective_iff_map_eq_zero _).2 fun m hm ↦ ?_
  have hres : toOpenₗ R M (basicOpen a) m = 0 :=
    congrArg ((structureSheafInType R M).1.map (homOfLE haU).op) hm
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalizedModule.eq_zero_iff (.powers a) (toOpenₗ R M (basicOpen a))).1 hres
  exact (ha.pow k).right_eq_zero_of_smul hk

/-- **Algebraic Hartogs principle.** Let `a, b` be a weakly `M`-regular sequence. If `D(a)` and
`D(b)` lie in the open subset `U` of `Spec R`, then `M → M~(U)` is bijective: every section of `M~`
over `U` comes from a unique element of `M`. -/
theorem toOpenₗ_bijective_of_isWeaklyRegular {U : Opens (PrimeSpectrum.Top R)} {a b : R}
    (h : IsWeaklyRegular M [a, b]) (haU : basicOpen a ≤ U) (hbU : basicOpen b ≤ U) :
    Function.Bijective (toOpenₗ R M U) := by
  have ha : IsSMulRegular M a := ((isWeaklyRegular_cons_iff M a [b]).1 h).1
  refine ⟨toOpenₗ_injective_of_isSMulRegular ha haU, fun s ↦ ?_⟩
  -- On `D(a)` and `D(b)` the section `s` is a fraction `x / aⁿ`, respectively `y / bᵐ`.
  obtain ⟨⟨x, _, n, rfl⟩, hx⟩ := IsLocalizedModule.surj (.powers a)
    (toOpenₗ R M (basicOpen a)) ((structureSheafInType R M).1.map (homOfLE haU).op s)
  obtain ⟨⟨y, _, m, rfl⟩, hy⟩ := IsLocalizedModule.surj (.powers b)
    (toOpenₗ R M (basicOpen b)) ((structureSheafInType R M).1.map (homOfLE hbU).op s)
  have hxp (p : PrimeSpectrum.Top R) (hp : p ∈ basicOpen a) :
      a ^ n • s.1 ⟨p, haU hp⟩ = LocalizedModule.mk x 1 :=
    congrArg (fun t ↦ t.1 ⟨p, hp⟩) hx
  have hyp (p : PrimeSpectrum.Top R) (hp : p ∈ basicOpen b) :
      b ^ m • s.1 ⟨p, hbU hp⟩ = LocalizedModule.mk y 1 :=
    congrArg (fun t ↦ t.1 ⟨p, hp⟩) hy
  -- The two fractions agree on `D(ab)`, so `(ab)ᵏ (bᵐ x - aⁿ y) = 0`.
  have hab : toOpenₗ R M (basicOpen (a * b)) (b ^ m • x - a ^ n • y) = 0 := by
    refine Subtype.ext (funext fun p ↦ ?_)
    obtain ⟨hpa, hpb⟩ : p.1 ∈ basicOpen a ∧ p.1 ∈ basicOpen b := by
      simpa [PrimeSpectrum.basicOpen_mul] using p.2
    -- Evaluate the section `toOpenₗ (bᵐ x - aⁿ y)`, the family of fractions `(bᵐ x - aⁿ y) / 1`,
    -- at `p`.
    change LocalizedModule.mk (b ^ m • x - a ^ n • y) 1 = 0
    rw [← LocalizedModule.mkLinearMap_apply, map_sub, map_smul, map_smul,
      LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply, ← hxp p.1 hpa,
      ← hyp p.1 hpb]
    exact sub_eq_zero.2 (smul_comm _ _ _)
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalizedModule.eq_zero_iff (.powers (a * b)) (toOpenₗ R M (basicOpen (a * b)))).1 hab
  -- Cancelling `aᵏ` gives `bᵏ⁺ᵐ x = aⁿ bᵏ y`, so `x = aⁿ c` since `b` is regular modulo `a`.
  have hbk : b ^ k • (b ^ m • x - a ^ n • y) = 0 :=
    (ha.pow k).right_eq_zero_of_smul (by rwa [smul_smul, ← mul_pow])
  have hxn : x ∈ a ^ n • (⊤ : Submodule R M) := by
    refine (Submodule.Quotient.mk_eq_zero _).1
      ((h.isSMulRegular_quotSMulTop_pow n (k + m)).right_eq_zero_of_smul ?_)
    rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add, smul_comm (b ^ k)] at hbk
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hbk]
    exact Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial
  obtain ⟨c, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hxn
  -- Now `s` and `c` agree on `D(a)`, hence on `U`, as `aⁿ` acts invertibly on `M~(D(a))`.
  refine ⟨c, res_injective_of_isSMulRegular haU ha inf_le_right ?_⟩
  have hc : (structureSheafInType R M).1.map (homOfLE haU).op (toOpenₗ R M U c) =
      toOpenₗ R M (basicOpen a) c := by
    rw [toOpenₗ_eq_const, toOpenₗ_eq_const, res_const]
  refine IsLocalizedModule.smul_injective (toOpenₗ R M (basicOpen a))
    (⟨a ^ n, n, rfl⟩ : Submonoid.powers a) ?_
  simp only [hc, hx, Submonoid.smul_def, map_smul]

end StructureSheaf

variable {R : CommRingCat.{u}}

/-- **Hartogs principle for `M~` on `Spec R`.** Let `M` be a finite module over a Noetherian ring
`R` and `U` an open subset of `Spec R` such that `depth M_p ≥ 2` for every prime `p ∉ U`. Then
`M → M~(U)` is bijective: every section of `M~` over `U` comes from a unique element of `M`.
Stacks, Lemma 31.5.11 (0E9I), for the affine scheme `Spec R` and `M~`, with `M_p` the stalk
of `M~` at `p`. -/
@[stacks 0E9I "affine case"]
theorem tilde_toOpen_bijective_of_two_le_depth [IsNoetherianRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] (U : (Spec R).Opens)
    (h : ∀ p : PrimeSpectrum R, p ∉ U → 2 ≤ depth (ModuleCat.of (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M))) :
    Function.Bijective (tilde.toOpen M U).hom := by
  -- The vanishing ideal of the closed set `Spec R ∖ U` contains a weakly `M`-regular pair.
  let I := PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ
  obtain ⟨rs, hlen, hmem, hreg⟩ := exists_isWeaklyRegular_of_le_depth_localizedModule I 2
    fun p _ hle ↦ h ⟨p, ‹_›⟩ <| by
      have hp : (⟨p, ‹_›⟩ : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus (I : Set R) := hle
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure] at hp
      exact U.isOpen.isClosed_compl.closure_subset hp
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hlen
  have hD (r : R) (hr : r ∈ [a, b]) : basicOpen r ≤ U := fun q hq ↦ by
    by_contra hqU
    exact hq ((PrimeSpectrum.mem_vanishingIdeal _ _).1 (hmem r hr) q hqU)
  -- By definition, `tilde.toOpen M U` is `toOpenₗ R M U` followed by an isomorphism of modules of
  -- sections; the composite is unfolded by `exact`, as Mathlib states no lemma for it.
  exact ((tilde.modulesSpecToSheafIso M).app _).symm.toLinearEquiv.bijective.comp
    (StructureSheaf.toOpenₗ_bijective_of_isWeaklyRegular hreg (hD a (by simp)) (hD b (by simp)))

end TauCeti.AlgebraicGeometry
