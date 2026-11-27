/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import TauCeti.NumberTheory.Padics.Complex.GaloisAction
public import TauCeti.RepresentationTheory.Continuous.BanachRep.Basic

import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Surjectivity
import TauCeti.NumberTheory.Cyclotomic.CyclotomicCharacter
import TauCeti.NumberTheory.Padics.AlgebraicClosure.NormalizedTrace
import TauCeti.NumberTheory.Padics.Complex.FixedPoints
import TauCeti.NumberTheory.Padics.UnitsCharacter
import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Operations

/-!
# Tate twists of `ℂ_p` and their Galois invariants

For an arbitrary intermediate field `K` of `PadicAlgCl p / ℚ_p`, this file defines the
continuous cyclotomic character on the native Galois group `Gal(PadicAlgCl p / K)` and the
Tate twists `ℂ_p(i)` as continuous representations on the fixed carrier `ℂ_p` and as bundled
Banach representations. The computation of their invariants below assumes `K/ℚ_p` finite.

Let `K` be a finite extension of `ℚ_p` inside `PadicAlgCl p`, let `G_K = Gal(PadicAlgCl p / K)`
act on `ℂ_p` by continuity, and let `χ : G_K → ℤ_pˣ` be the cyclotomic character (Mathlib's
`cyclotomicCharacter` of the underlying ring automorphism). For `i ∈ ℤ` the Tate twist `ℂ_p(i)` is
`ℂ_p` with `σ` acting by `x ↦ χ(σ) ^ i σ(x)`. **Tate's theorem** computes its invariants: they are
`K` for `i = 0`, which is the Ax–Sen–Tate theorem, and `0` for `i ≠ 0`.

The vanishing is first proved for the whole group `G_{ℚ_p}`. Let `T` be the normalized trace to
`ℚ_p` and `F = ℚ_p(μ_{p^∞})`, on which `‖T z‖ ≤ p ‖z‖`
(`PadicAlgCl.norm_normalizedTrace_le`). The elements of `ℂ_p` fixed by the kernel of `χ` form the
closure of `F` (Ax–Sen–Tate). For `σ ∈ G_{ℚ_p}` and `w ∈ F` the element `1 - (σ w - w)` of `F`
has normalized trace `1`, so `1 ≤ p ‖1 - (σ z - z)‖` for every `z` in the closure of `F`. If
`σ y = χ(σ) ^ (-i) y` for all `σ` and `w ∈ F`, choose `γ` fixing `w` with `b = χ(γ) ^ (-i) ≠ 1`;
then `z = (b - 1)⁻¹ y w` is fixed by the kernel of `χ` and `γ z - z = y w`, so
`1 ≤ p ‖1 - y w‖`. By continuity this holds for `w` in the closure of `F`, which contains `y⁻¹`
if `y ≠ 0`; at `w = y⁻¹` it reads `1 ≤ 0`.

The vanishing descends to `G_K` by a twisted trace. For `a ∈ K` the sum over the embeddings
`φ : K → PadicAlgCl p`, with extensions `g_φ ∈ G_{ℚ_p}`, of `χ(g_φ) ^ i g_φ(a y)` is invariant
in `ℂ_p(i)` under all of `G_{ℚ_p}`, hence zero. It equals `∑_φ φ(a) χ(g_φ) ^ i g_φ(y)`, and the
embeddings are linearly independent characters of `K` (Dedekind), so `y = 0`.

## Main definitions

* `TauCeti.padicAlgClContinuousCyclotomicCharacter`: the continuous cyclotomic character on
  the native Galois group `Gal(PadicAlgCl p / K)`.
* `TauCeti.padicComplexTateTwistContinuousRep`: the twist on the fixed carrier `ℂ_p`.
* `TauCeti.padicComplexTateTwist`: the associated bundled Banach representation.

## Main results

* `TauCeti.padicAlgClContinuousCyclotomicCharacter_apply`,
  `TauCeti.padicComplexTateTwistContinuousRep_apply`, and
  `TauCeti.padicComplexTateTwist_ρ_apply`: the character and action equations for arbitrary `K`.
* `PadicComplex.eq_zero_of_forall_cyclotomicCharacter_zpow_mul_smul_eq_ratPadic`: `ℂ_p(i)` has
  no nonzero `G_{ℚ_p}`-invariants for `i ≠ 0`.
* `PadicComplex.eq_zero_of_forall_cyclotomicCharacter_zpow_mul_smul_eq`: `ℂ_p(i)` has no nonzero
  `G_K`-invariants for `i ≠ 0` and `K` finite over `ℚ_p`.
* `PadicComplex.forall_cyclotomicCharacter_zpow_mul_smul_eq_iff`: the `G_K`-invariants of
  `ℂ_p(i)` are `K` for `i = 0` and `0` otherwise: Tate's computation of `H⁰(G_K, ℂ_p(i))`.

## References

* J. Tate, *p-divisible groups*, Proceedings of a Conference on Local Fields (Driebergen, 1966),
  Springer, 1967, §3.3, Theorem 2.
* O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), Theorem 2.2.7
  and §14.1.
* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois representations*, §4.3.5,
  Proposition 4.46.

The proof over `G_{ℚ_p}` and the descent through linearly independent characters are adapted from
`New.Period.eq_zero_of_smul_eq_cyclotomicGp_zpow_smul`,
`New.Period.tate_eq_zero_of_cyclotomicGp_twist`
(`src/Lib/PadicHodge/TateSen.lean`) and `New.Period.mem_span_fixed`
(`src/Lib/ClassField/GaloisCohomology/KummerCyclicClasses.lean`) of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open UniformSpace.Completion IntermediateField

namespace PadicComplex

variable {p : ℕ} [hp : Fact p.Prime]

/-- The scalar `χ(σ) ^ i ∈ ℂ_p` by which `σ` is twisted in `ℂ_p(i)`. -/
private noncomputable def twist (i : ℤ) (σ : PadicAlgCl p ≃+* PadicAlgCl p) : ℂ_[p] :=
  algebraMap ℚ_[p] ℂ_[p] (((cyclotomicCharacter (PadicAlgCl p) p σ ^ i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])

private theorem twist_def (i : ℤ) (σ : PadicAlgCl p ≃+* PadicAlgCl p) :
    twist i σ =
      algebraMap ℚ_[p] ℂ_[p] (((cyclotomicCharacter (PadicAlgCl p) p σ ^ i : ℤ_[p]ˣ) : ℤ_[p]) :
        ℚ_[p]) :=
  rfl

private theorem twist_mul (i : ℤ) (σ τ : PadicAlgCl p ≃+* PadicAlgCl p) :
    twist i (σ * τ) = twist i σ * twist i τ := by
  simp [twist, mul_zpow]

/-- `twist_mul` for automorphisms over a subfield: the product of algebra automorphisms has the
product of the underlying ring automorphisms as its underlying ring automorphism. -/
private theorem twist_algEquiv_mul {K : Type*} [Field K] [Algebra K (PadicAlgCl p)] (i : ℤ)
    (σ τ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) :
    twist i (σ * τ).toRingEquiv = twist i σ.toRingEquiv * twist i τ.toRingEquiv :=
  twist_mul i σ.toRingEquiv τ.toRingEquiv

private theorem twist_ne_zero (i : ℤ) (σ : PadicAlgCl p ≃+* PadicAlgCl p) : twist i σ ≠ 0 := by
  simp [twist]

private theorem smul_twist {K : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
    [IsScalarTower ℚ_[p] K (PadicAlgCl p)] (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (i : ℤ)
    (τ : PadicAlgCl p ≃+* PadicAlgCl p) : σ • twist i τ = twist i τ := by
  rw [twist, ← algEquiv_restrictScalars_smul (R := ℚ_[p]), smul_algebraMap]

/-- The full cyclotomic extension `ℚ_p(μ_{p^∞})` inside `PadicAlgCl p`. -/
local notation "𝔽" => TauCeti.cyclotomicTower p ℚ_[p] (PadicAlgCl p)

/-- An element of `ℂ_p` fixed by every `σ ∈ G_{ℚ_p}` with trivial cyclotomic character lies in
the closure of `ℚ_p(μ_{p^∞})`, by the Ax–Sen–Tate theorem. -/
private theorem mem_closure_of_forall_smul_eq {x : ℂ_[p]}
    (hx : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv = 1 → σ • x = x) :
    x ∈ closure (Set.range fun w : 𝔽 ↦ ((w : PadicAlgCl p) : ℂ_[p])) := by
  rw [← fixedPoints_algEquiv_eq_closure]
  intro σ
  rw [← algEquiv_restrictScalars_smul (R := ℚ_[p])]
  refine hx _ ((TauCeti.mem_fixingSubgroup_adjoin_iff_cyclotomicCharacter_eq_one p).mp ?_)
  rw [← TauCeti.cyclotomicTower_def, IntermediateField.mem_fixingSubgroup_iff]
  exact fun w hw ↦ σ.commutes ⟨w, hw⟩

/-- **The trace estimate.** For `σ ∈ G_{ℚ_p}` and `z` in the closure of `ℚ_p(μ_{p^∞})`,
`1 ≤ p ‖1 - (σ z - z)‖`: on `ℚ_p(μ_{p^∞})` the element `1 - (σ z - z)` has normalized trace `1`,
and Tate's bound applies. -/
private theorem one_le_mul_norm_one_sub (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {z : ℂ_[p]}
    (hz : z ∈ closure (Set.range fun w : 𝔽 ↦ ((w : PadicAlgCl p) : ℂ_[p]))) :
    1 ≤ p * ‖1 - (σ • z - z)‖ := by
  refine closure_minimal (t := {z : ℂ_[p] | 1 ≤ p * ‖1 - (σ • z - z)‖}) ?_
    (isClosed_le continuous_const (by fun_prop)) hz
  rintro _ ⟨⟨w, hw⟩, rfl⟩
  set T := Algebra.normalizedTrace ℚ_[p] (PadicAlgCl p)
  have h_trace : T (1 - (σ w - w)) = 1 := by
    have h1 : T 1 = 1 := by
      simpa using Algebra.normalizedTrace_algebraMap_apply ℚ_[p] ℚ_[p] (PadicAlgCl p) 1
    -- The normalized trace is invariant under `σ`.
    have hσ : T (σ w) = T w := by
      simpa only [T, AlgEquiv.coe_toAlgHom] using
        Algebra.normalizedTrace_map ℚ_[p] (PadicAlgCl p) σ.toAlgHom w
    rw [map_sub, map_sub, h1, hσ, sub_self, sub_zero]
  have h_mem : 1 - (σ w - w) ∈ 𝔽 :=
    sub_mem (one_mem _) (sub_mem (TauCeti.apply_mem_cyclotomicTower σ hw) hw)
  have h := PadicAlgCl.norm_normalizedTrace_le h_mem
  rw [h_trace, norm_one] at h
  simpa [Set.mem_ofPred_eq, algEquiv_smul_coe, ← coe_one, ← coe_sub] using h

/-- Every `w ∈ ℚ_p(μ_{p^∞})` is fixed by some `γ ∈ G_{ℚ_p}` with `χ(γ) ^ i ≠ 1`, for `i ≠ 0`:
if `w ∈ ℚ_p(μ_{p^N})`, take `χ(γ) = 1 + p ^ (N + 1)`, which is not a root of unity. -/
private theorem exists_apply_eq_and_cyclotomicCharacter_zpow_ne_one {i : ℤ} (hi : i ≠ 0)
    {w : PadicAlgCl p} (hw : w ∈ 𝔽) :
    ∃ γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, γ w = w ∧
      cyclotomicCharacter (PadicAlgCl p) p γ.toRingEquiv ^ i ≠ 1 := by
  obtain ⟨N, hN⟩ := TauCeti.mem_cyclotomicTower_iff.mp hw
  have hcop : p.Coprime (1 + p ^ N * p) :=
    (Nat.coprime_add_mul_right_right p 1 (p ^ N)).mpr (Nat.coprime_one_right p)
  rw [← pow_succ] at hcop
  have hu : IsUnit ((1 + p ^ (N + 1) : ℕ) : ℤ_[p]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcop)
  obtain ⟨γ, hγ⟩ := TauCeti.surjective_localCyclotomicCharacter_ratPadic p hu.unit
  rw [TauCeti.localCyclotomicCharacter_apply] at hγ
  -- `γ • w = w` is `γ w = w` by `AlgEquiv.smul_def`
  refine ⟨γ, (forall_mem_adjoin_smul_eq_self_iff ℚ_[p]
    (M := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) γ).2
    (fun s (hs : s ^ p ^ N = 1) ↦ ?_) w hN, fun h ↦ ?_⟩
  · have h1 : PadicInt.toZModPow N ((1 + p ^ (N + 1) : ℕ) : ℤ_[p]) = 1 := by
      have h0 : ((p ^ (N + 1) : ℕ) : ZMod (p ^ N)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow p N.le_succ)
      rw [map_natCast, Nat.cast_add, Nat.cast_one, h0, add_zero]
    have := cyclotomicCharacter.spec p γ.toRingEquiv s hs
    rwa [hγ, IsUnit.unit_spec, h1, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hs, pow_one] at this
  · rw [hγ] at h
    have h' := congrArg (fun u : ℤ_[p]ˣ ↦ (u : ℤ_[p])) (pow_natAbs_eq_one.mpr h)
    simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h'
    have h'' : (1 + p ^ (N + 1)) ^ i.natAbs = 1 := by exact_mod_cast h'
    have : 1 < p ^ (N + 1) := Nat.one_lt_pow N.succ_ne_zero hp.out.one_lt
    rcases Nat.pow_eq_one.mp h'' with h | h
    · omega
    · exact hi (Int.natAbs_eq_zero.mp h)

/-- The key estimate in Tate's argument: if `y` is invariant in `ℂ_p(i)`, `i ≠ 0`, then
`1 ≤ p ‖1 - y w‖` for every `w ∈ ℚ_p(μ_{p^∞})`. -/
private theorem one_le_mul_norm_one_sub_mul {i : ℤ} (hi : i ≠ 0) {y : ℂ_[p]}
    (hy : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, twist i σ.toRingEquiv * σ • y = y)
    {w : PadicAlgCl p} (hw : w ∈ 𝔽) : 1 ≤ p * ‖1 - y * (w : ℂ_[p])‖ := by
  obtain ⟨γ, hγw, hγ⟩ := exists_apply_eq_and_cyclotomicCharacter_zpow_ne_one hi hw
  -- `γ` multiplies `y` by `c = χ(γ) ^ (-i) ≠ 1`.
  set c := (twist i γ.toRingEquiv)⁻¹
  have hc : c - 1 ≠ 0 := by
    refine sub_ne_zero.mpr fun h ↦ hγ (Units.ext (PadicInt.ext ?_))
    simpa [c, twist, inv_eq_one] using h
  have hγy : γ • y = c * y := by
    rw [eq_inv_mul_iff_mul_eq₀ (twist_ne_zero i _), hy]
  have hσc (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : σ • (c - 1)⁻¹ = (c - 1)⁻¹ := by
    rw [smul_inv'', smul_sub, smul_one, smul_inv'', smul_twist]
  -- `z = (c - 1)⁻¹ y w` is fixed by the kernel of `χ`, and `γ z - z = y w`.
  have hz : (c - 1)⁻¹ * (y * (w : ℂ_[p])) ∈
      closure (Set.range fun w : 𝔽 ↦ ((w : PadicAlgCl p) : ℂ_[p])) := by
    refine mem_closure_of_forall_smul_eq fun σ hσ ↦ ?_
    have hσy : σ • y = y := by simpa [twist, hσ] using hy σ
    rw [smul_mul', smul_mul', hσc, hσy, algEquiv_smul_coe,
      TauCeti.apply_eq_of_cyclotomicCharacter_eq_one hσ hw]
  have h_diff : γ • ((c - 1)⁻¹ * (y * (w : ℂ_[p]))) - (c - 1)⁻¹ * (y * (w : ℂ_[p])) =
      y * w := by
    rw [smul_mul', smul_mul', hσc, hγy, algEquiv_smul_coe, hγw]
    field_simp
  have h := one_le_mul_norm_one_sub γ hz
  rwa [h_diff] at h

/-- **Tate's theorem for `G_{ℚ_p}`.** For `i ≠ 0`, the only element `y ∈ ℂ_p` with
`χ(σ) ^ i σ(y) = y` for every `σ ∈ Gal(PadicAlgCl p / ℚ_p)` is `0`: the Tate twist `ℂ_p(i)` has no
nonzero Galois invariants. -/
theorem eq_zero_of_forall_cyclotomicCharacter_zpow_mul_smul_eq_ratPadic {i : ℤ} (hi : i ≠ 0)
    {y : ℂ_[p]} (hy : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      algebraMap ℚ_[p] ℂ_[p]
          (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv ^ i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
        σ • y = y) : y = 0 := by
  by_contra hy0
  -- `y⁻¹` is fixed by the kernel of `χ`, so it lies in the closure of `ℚ_p(μ_{p^∞})`, where the
  -- continuous function `x ↦ p ‖1 - y x‖` is at least `1`; but it vanishes at `y⁻¹`.
  have h_inv : y⁻¹ ∈ closure (Set.range fun w : 𝔽 ↦ ((w : PadicAlgCl p) : ℂ_[p])) := by
    refine mem_closure_of_forall_smul_eq fun σ hσ ↦ ?_
    have hσy : σ • y = y := by simpa [hσ] using hy σ
    rw [smul_inv'', hσy]
  have h := closure_minimal (t := {x : ℂ_[p] | 1 ≤ p * ‖1 - y * x‖})
    (Set.range_subset_iff.mpr fun w ↦ one_le_mul_norm_one_sub_mul hi hy w.property)
    (isClosed_le continuous_const (by fun_prop)) h_inv
  simp [mul_inv_cancel₀ hy0] at h
  linarith

section Descent

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- Invariance in `ℂ_p(i)` under `G_K` is invariance under the elements of `G_{ℚ_p}` fixing `K`. -/
private theorem twist_mul_smul_eq_of_forall_apply_eq {i : ℤ} {y : ℂ_[p]}
    (hy : ∀ σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p, twist i σ.toRingEquiv * σ • y = y)
    {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : ∀ a : K, σ a = a) :
    twist i σ.toRingEquiv * σ • y = y := by
  -- `σ` as an automorphism over `K`.
  set σK := K.fixingSubgroupEquiv ⟨σ, (mem_fixingSubgroup_iff _ σ).2 fun a ha ↦ hσ ⟨a, ha⟩⟩
  have hσK : σK.restrictScalars ℚ_[p] = σ :=
    AlgEquiv.ext fun x ↦ congrFun (coe_fixingSubgroupEquiv_apply K _) x
  have h := hy σK
  rwa [← algEquiv_restrictScalars_smul (R := ℚ_[p]), hσK] at h

/-- If `y` is invariant in `ℂ_p(i)` under `G_K`, then for `a ∈ K` the twisted conjugate
`χ(g) ^ i g(a y)`, `g ∈ G_{ℚ_p}`, only depends on the restriction of `g` to `K`. -/
private theorem twist_mul_smul_eq_of_apply_eq {i : ℤ} {y : ℂ_[p]}
    (hy : ∀ σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p, twist i σ.toRingEquiv * σ • y = y)
    {g g' : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hgg' : ∀ a : K, g a = g' a) (a : K) :
    twist i g.toRingEquiv * g • ((a : PadicAlgCl p) * y : ℂ_[p]) =
      twist i g'.toRingEquiv * g' • ((a : PadicAlgCl p) * y : ℂ_[p]) := by
  -- `g = g' u` with `u` fixing `K`.
  set u := g'⁻¹ * g
  have hu : ∀ b : K, u b = b := fun b ↦ by
    simp [u, AlgEquiv.mul_apply, hgg' b]
  have hg : g = g' * u := by simp [u]
  have hu_y := twist_mul_smul_eq_of_forall_apply_eq hy hu
  rw [hg]
  calc twist i (g' * u).toRingEquiv * (g' * u) • ((a : PadicAlgCl p) * y : ℂ_[p])
      = twist i g'.toRingEquiv *
          g' • (twist i u.toRingEquiv * u • ((a : PadicAlgCl p) * y : ℂ_[p])) := by
        rw [twist_algEquiv_mul,
          mul_smul, smul_mul' g', smul_twist, mul_assoc]
    _ = twist i g'.toRingEquiv * g' • ((a : PadicAlgCl p) * y : ℂ_[p]) := by
        rw [smul_mul' u, algEquiv_smul_coe, hu, mul_left_comm, hu_y]

variable (K) in
/-- Every `ℚ_p`-embedding of `K` into `PadicAlgCl p` extends to an automorphism. -/
private theorem exists_algEquiv_apply_eq (φ : K →ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ a : K, g a = φ a :=
  ⟨(Algebra.IsAlgebraic.algEquivEquivAlgHom ℚ_[p] (PadicAlgCl p)).symm
    (φ.liftNormal (PadicAlgCl p)), fun a ↦ φ.liftNormal_commutes (PadicAlgCl p) a⟩

/-- **Tate's theorem.** Let `K` be a finite extension of `ℚ_p` inside `PadicAlgCl p`. For `i ≠ 0`,
the only element `y ∈ ℂ_p` with `χ(σ) ^ i σ(y) = y` for every `σ ∈ Gal(PadicAlgCl p / K)` is `0`:
the Tate twist `ℂ_p(i)` has no nonzero `G_K`-invariants. -/
theorem eq_zero_of_forall_cyclotomicCharacter_zpow_mul_smul_eq [FiniteDimensional ℚ_[p] K]
    {i : ℤ} (hi : i ≠ 0) {y : ℂ_[p]} (hy : ∀ σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p,
      algebraMap ℚ_[p] ℂ_[p]
          (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv ^ i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
        σ • y = y) : y = 0 := by
  classical
  simp only [← twist_def] at hy
  choose g hg using exists_algEquiv_apply_eq K
  -- The twisted conjugates of `y` by the extensions `g φ` of the embeddings `φ` of `K`.
  set c : (K →ₐ[ℚ_[p]] PadicAlgCl p) → ℂ_[p] := fun φ ↦ twist i (g φ).toRingEquiv * g φ • y
  -- For `a ∈ K`, the twisted trace `∑_φ φ(a) c(φ)` of `a y` is invariant in `ℂ_p(i)`, so it is `0`.
  have hsum (a : K) : ∑ φ, ((φ a : PadicAlgCl p) : ℂ_[p]) * c φ = 0 := by
    have h_eq : ∑ φ, ((φ a : PadicAlgCl p) : ℂ_[p]) * c φ =
        ∑ φ, twist i (g φ).toRingEquiv * g φ • ((a : PadicAlgCl p) * y : ℂ_[p]) := by
      refine Finset.sum_congr rfl fun φ _ ↦ ?_
      rw [smul_mul', algEquiv_smul_coe, hg, mul_left_comm]
    rw [h_eq]
    refine eq_zero_of_forall_cyclotomicCharacter_zpow_mul_smul_eq_ratPadic hi fun h ↦ ?_
    rw [← twist_def]
    rw [Finset.smul_sum, Finset.mul_sum]
    -- Composition with `h` permutes the embeddings.
    let e : (K →ₐ[ℚ_[p]] PadicAlgCl p) ≃ (K →ₐ[ℚ_[p]] PadicAlgCl p) :=
      { toFun φ := (h : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).comp φ
        invFun φ := (h.symm : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).comp φ
        left_inv φ := AlgHom.ext fun _ ↦ h.symm_apply_apply _
        right_inv φ := AlgHom.ext fun _ ↦ h.apply_symm_apply _ }
    have he (φ : K →ₐ[ℚ_[p]] PadicAlgCl p) :
        e φ = (h : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).comp φ :=
      rfl
    refine Fintype.sum_equiv e _ _ fun φ ↦ ?_
    rw [smul_mul', smul_twist, ← mul_assoc, ← twist_algEquiv_mul, ← mul_smul]
    refine twist_mul_smul_eq_of_apply_eq hy (fun b ↦ ?_) a
    rw [AlgEquiv.mul_apply, hg, hg, he, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  -- The embeddings are linearly independent characters of `K` (Dedekind), so each `c φ` is `0`.
  let f : (K →ₐ[ℚ_[p]] PadicAlgCl p) → (K →* ℂ_[p]) := fun φ ↦
    (coeRingHom : PadicAlgCl p →+* ℂ_[p]).toMonoidHom.comp (φ : K →* PadicAlgCl p)
  have hf : Function.Injective f := fun φ ψ h ↦ AlgHom.ext fun a ↦
    coe_injective _ (DFunLike.congr_fun h a)
  have hc := Fintype.linearIndependent_iff.mp ((linearIndependent_monoidHom K ℂ_[p]).comp f hf) c
    (funext fun a ↦ by simpa [f, mul_comm, coeRingHom] using hsum a)
    (IsScalarTower.toAlgHom ℚ_[p] K _)
  simpa [c, twist_ne_zero, smul_eq_zero_iff_eq] using hc

end Descent

/-- **Tate's calculation of `H⁰(G_K, ℂ_p(i))`.** Let `K` be a finite extension of `ℚ_p` inside
`PadicAlgCl p`. The elements of `ℂ_p` with `χ(σ) ^ i σ(x) = x` for every
`σ ∈ Gal(PadicAlgCl p / K)` are those of `K` for `i = 0` (the Ax–Sen–Tate theorem) and only `0`
for `i ≠ 0`. -/
theorem forall_cyclotomicCharacter_zpow_mul_smul_eq_iff
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (i : ℤ) (x : ℂ_[p]) :
    (∀ σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p,
      algebraMap ℚ_[p] ℂ_[p]
          (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv ^ i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
        σ • x = x) ↔
      if i = 0 then x ∈ Set.range fun a : K ↦ ((a : PadicAlgCl p) : ℂ_[p]) else x = 0 := by
  split_ifs with hi
  · subst hi
    simp only [zpow_zero, Units.val_one, PadicInt.coe_one, map_one, one_mul]
    rw [← fixedPoints_algEquiv_eq_range]
    exact MulAction.mem_fixedPoints.symm
  · exact ⟨eq_zero_of_forall_cyclotomicCharacter_zpow_mul_smul_eq hi, by rintro rfl; simp⟩

end PadicComplex

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- The continuous cyclotomic character on the native Galois group `Gal(PadicAlgCl p / K)`. -/
noncomputable def padicAlgClContinuousCyclotomicCharacter :
    (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →ₜ* ℤ_[p]ˣ :=
  ⟨(cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (PadicAlgCl p)),
    cyclotomicCharacter.continuous p K (PadicAlgCl p)⟩

/-- The continuous cyclotomic character is Mathlib's character of the underlying automorphism. -/
@[simp]
theorem padicAlgClContinuousCyclotomicCharacter_apply
    (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) :
    padicAlgClContinuousCyclotomicCharacter p K σ =
      cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv := by
  simp [padicAlgClContinuousCyclotomicCharacter]

/-- The Tate twist `ℂ_p(i)` as a continuous representation on the fixed carrier `ℂ_p`. -/
noncomputable def padicComplexTateTwistContinuousRep (i : ℤ) :
    ContinuousRep (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) ℚ_[p] ℂ_[p] :=
  (ContinuousRep.ofDistribMulAction _ ℚ_[p] ℂ_[p]).twist
    ((padicIntUnitsInclusion p).comp (padicAlgClContinuousCyclotomicCharacter p K ^ i))

/-- The action on the fixed carrier `ℂ_p` is the Galois action multiplied by `χ(σ)^i`. -/
@[simp]
theorem padicComplexTateTwistContinuousRep_apply (i : ℤ)
    (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (x : ℂ_[p]) :
    padicComplexTateTwistContinuousRep p K i σ x =
      (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv ^ i : ℤ_[p]ˣ) : ℤ_[p]) :
        ℚ_[p]) • (σ • x) := by
  simp only [padicComplexTateTwistContinuousRep, ContinuousRep.twist_apply,
    ContinuousRep.ofDistribMulAction_apply, ContinuousMonoidHom.comp_toFun,
    ContinuousMonoidHom.zpow_apply, coe_padicIntUnitsInclusion_apply,
    padicAlgClContinuousCyclotomicCharacter_apply]

/-- The Tate twist `ℂ_p(i)` as a Banach representation of `G_K` over `ℚ_p`. -/
noncomputable abbrev padicComplexTateTwist (i : ℤ) :
    BanachRep.{0} ℚ_[p] (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) :=
  BanachRep.of (padicComplexTateTwistContinuousRep p K i)

/-- The action in the Tate twist is the Galois action multiplied by `χ(σ)^i`.
Simplification uses `padicComplexTateTwistContinuousRep_apply` on the underlying action. -/
theorem padicComplexTateTwist_ρ_apply (i : ℤ)
    (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (x : ℂ_[p]) :
    (padicComplexTateTwist p K i).ρ σ x =
      (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv ^ i : ℤ_[p]ˣ) : ℤ_[p]) :
        ℚ_[p]) • (σ • x) :=
  padicComplexTateTwistContinuousRep_apply p K i σ x

end TauCeti
