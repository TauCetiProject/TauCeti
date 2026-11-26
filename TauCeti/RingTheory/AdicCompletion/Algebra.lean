/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import TauCeti.RingTheory.Ideal.Maps

/-!
# The powers of the extended ideal in the adic completion of a ring

Let `I` be a finitely generated ideal of a commutative ring `R` and `R̂ = AdicCompletion I R`.
The kernel of the projection `R̂ → R ⧸ I ^ n` is the extension `I ^ n R̂` of `I ^ n`. Mathlib
records the case `n = 1` (`AdicCompletion.ker_evalOneₐ_eq_map`); the general case identifies
the `I R̂`-adic filtration of `R̂` with the kernels of the projections, so that
`R̂ ⧸ I ^ n R̂ ≃ R ⧸ I ^ n`. Consequently the canonical map `R → R̂` identifies `I ^ n` with the
preimage of `I ^ n R̂`, and every element of `R̂` is congruent modulo `I ^ n R̂` to the image of an
element of `R`, so the image of `R` is dense in `R̂` for the `I R̂`-adic topology.

If `R` is Hausdorff for the `I`-adic topology, then `R → R̂` is injective, so `R̂` has the
exponential characteristic of `R`.

## Main results

* `AdicCompletion.ker_evalₐ_eq_map_pow`: the kernel of `R̂ → R ⧸ I ^ n` is `I ^ n R̂`.
* `AdicCompletion.quotientMapPowAlgEquiv`: the isomorphism of `R`-algebras
  `R̂ ⧸ I ^ n R̂ ≃ R ⧸ I ^ n`.
* `AdicCompletion.algebraMap_mem_map_pow_iff`: the image of `x ∈ R` lies in `I ^ n R̂` if and
  only if `x ∈ I ^ n`.
* `AdicCompletion.exists_sub_algebraMap_mem_map_pow`: every element of `R̂` is congruent
  modulo `I ^ n R̂` to the image of an element of `R`.
* `AdicCompletion.of_smul`: the canonical map `N → N̂` from an `R̂`-module to its `I`-adic
  completion is `R̂`-linear.
* `AdicCompletion.ringHom_ext`: two ring homomorphisms out of `R̂` into a ring that is Hausdorff
  for an ideal `J`, which carry `I R̂` into `J` and agree on the image of `R`, are equal.
* `AdicCompletion.quotientMap_algebraMap_bijective`: the map `R ⧸ I ^ n → R̂ ⧸ (I R̂) ^ n` induced
  by `R → R̂` is bijective; `AdicCompletion.quotientMap_algebraMap_bijective_one` is the case
  `n = 1`.
* `AdicCompletion.denseRange_algebraMap`: the image of `R` is dense in `R̂` for the `I R̂`-adic
  topology.
* `AdicCompletion.expChar`: the `I`-adic completion of an `I`-adically Hausdorff ring has the
  exponential characteristic of the ring.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.2.
-/

public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- For a finitely generated ideal `I`, the kernel of the projection of the adic completion
onto `R ⧸ I ^ n` is the extension of `I ^ n` to the completion. -/
theorem ker_evalₐ_eq_map_pow (fg : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n) = (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  ext x
  trans x ∈ (eval I R n).ker
  · have eq : (I ^ n • ⊤ : Ideal R) = I ^ n := by simp
    rw [RingHom.mem_ker, ← factor_eval_eq_evalₐ I x eq.le, LinearMap.mem_ker]
    -- The factor map is the quotient equivalence from which `evalₐ` is built.
    exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R eq).injective
  · simp [← pow_smul_top_eq_ker_eval fg, Ideal.smul_top_eq_map]

/-- For a finitely generated ideal `I`, the adic completion modulo the extension of `I ^ n` is
`R ⧸ I ^ n`: the isomorphism is induced by the projection `R̂ → R ⧸ I ^ n`. -/
noncomputable def quotientMapPowAlgEquiv (fg : I.FG) (n : ℕ) :
    (AdicCompletion I R ⧸ (I ^ n).map (algebraMap R (AdicCompletion I R))) ≃ₐ[R] R ⧸ I ^ n :=
  (Ideal.quotientEquivAlgOfEq R (ker_evalₐ_eq_map_pow fg n).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I n))

/-- The isomorphism `R̂ ⧸ I ^ n R̂ ≃ R ⧸ I ^ n` sends the class of `x` to its projection. -/
@[simp]
theorem quotientMapPowAlgEquiv_mk (fg : I.FG) (n : ℕ) (x : AdicCompletion I R) :
    quotientMapPowAlgEquiv fg n (Ideal.Quotient.mk _ x) = evalₐ I n x := by
  simp [quotientMapPowAlgEquiv]

/-- An element of `R` maps into the extension of `I ^ n` to the adic completion if and only if it
lies in `I ^ n`. -/
@[simp]
theorem algebraMap_mem_map_pow_iff (n : ℕ) {x : R} :
    algebraMap R (AdicCompletion I R) x ∈ (I ^ n).map (algebraMap R (AdicCompletion I R)) ↔
      x ∈ I ^ n := by
  refine ⟨fun h ↦ ?_, Ideal.mem_map_of_mem _⟩
  have hker : (I ^ n).map (algebraMap R (AdicCompletion I R)) ≤ RingHom.ker (evalₐ I n) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp [algebraMap_apply, Ideal.Quotient.eq_zero_iff_mem, hy]
  simpa [algebraMap_apply, Ideal.Quotient.eq_zero_iff_mem] using hker h

/-- For a finitely generated ideal `I`, every element of the adic completion is congruent modulo
the extension of `I ^ n` to the image of an element of `R`. -/
theorem exists_sub_algebraMap_mem_map_pow (fg : I.FG) (n : ℕ) (x : AdicCompletion I R) :
    ∃ y : R, x - algebraMap R (AdicCompletion I R) y ∈
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  refine ⟨y, ?_⟩
  rw [← ker_evalₐ_eq_map_pow fg, RingHom.mem_ker, map_sub, ← hy]
  exact sub_eq_zero.mpr (evalₐ_of I n y).symm

/-- For a finitely generated ideal `I` and a module `N` over the completion `R̂` (with compatible
`R`-module structure), the canonical map `N → N̂` into the `I`-adic completion of `N` is
`R̂`-linear, and not only `R`-linear. -/
theorem of_smul (fg : I.FG) {N : Type*} [AddCommGroup N] [Module (AdicCompletion I R) N]
    [Module R N] [IsScalarTower R (AdicCompletion I R) N] (x : AdicCompletion I R) (m : N) :
    of I N (x • m) = x • of I N m := by
  ext n
  -- `x` is the image of some `y ∈ R` up to an element `d` of `I ^ n R̂`
  obtain ⟨y, hy⟩ := exists_sub_algebraMap_mem_map_pow fg n x
  obtain ⟨d, hd, rfl⟩ : ∃ d ∈ (I ^ n).map (algebraMap R (AdicCompletion I R)),
      x = d + algebraMap R _ y := ⟨_, hy, (sub_add_cancel _ _).symm⟩
  -- so `d • m` vanishes in `N ⧸ I ^ n N`, and `d` acts by zero on the `n`-th level of `N̂`
  have hm : d • m ∈ (I ^ n • ⊤ : Submodule R N) := by
    have h : d • m ∈ ((I ^ n).map (algebraMap R (AdicCompletion I R)) • ⊤ :
        Submodule (AdicCompletion I R) N) := Submodule.smul_mem_smul hd Submodule.mem_top
    rwa [← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars,
      Submodule.restrictScalars_top] at h
  have hx : evalₐ I n d = 0 := by rwa [← RingHom.mem_ker, ker_evalₐ_eq_map_pow fg]
  simpa [add_smul, smul_eval, hx, (Submodule.Quotient.mk_eq_zero _).mpr hm] using
    val_smul_eq_evalₐ_smul I n d (Submodule.Quotient.mk m)

/-- **Ring homomorphisms out of the adic completion are determined on `R`.** For a finitely
generated ideal `I`, two ring homomorphisms `R̂ → T` into a ring that is Hausdorff for an ideal `J`,
which both carry `I R̂` into `J` and agree on the image of `R`, are equal. -/
theorem ringHom_ext {T : Type*} [CommRing T] {J : Ideal T} [IsHausdorff J T] (fg : I.FG)
    {g h : AdicCompletion I R →+* T}
    (hg : I.map (algebraMap R (AdicCompletion I R)) ≤ J.comap g)
    (hh : I.map (algebraMap R (AdicCompletion I R)) ≤ J.comap h)
    (H : g.comp (algebraMap R (AdicCompletion I R)) = h.comp (algebraMap R (AdicCompletion I R))) :
    g = h := by
  refine RingHom.ext (congrFun (IsHausdorff.funext' J fun n x ↦ ?_))
  obtain ⟨y, hy⟩ := exists_sub_algebraMap_mem_map_pow fg n x
  rw [Ideal.map_pow] at hy
  have hy' := RingHom.congr_fun H y
  simp only [RingHom.comp_apply] at hy'
  rw [Ideal.Quotient.eq, ← sub_add_cancel x (algebraMap R _ y), map_add, map_add, hy',
    add_sub_add_right_eq_sub]
  exact sub_mem (Ideal.map_mem_pow_of_le_comap g hg hy) (Ideal.map_mem_pow_of_le_comap h hh hy)

/-- For a finitely generated ideal `I`, the map `R ⧸ I ^ n → R̂ ⧸ (I R̂) ^ n` induced by the
canonical map `R → R̂` is bijective: `R` and its `I`-adic completion have the same reductions. -/
theorem quotientMap_algebraMap_bijective (fg : I.FG) (n : ℕ)
    {H : I ^ n ≤ ((I.map (algebraMap R (AdicCompletion I R))) ^ n).comap
      (algebraMap R (AdicCompletion I R))} :
    Function.Bijective (Ideal.quotientMap _ (algebraMap R (AdicCompletion I R)) H) := by
  refine ⟨Ideal.quotientMap_injective' fun x hx ↦ ?_, fun x ↦ ?_⟩
  · rwa [Ideal.mem_comap, ← Ideal.map_pow, algebraMap_mem_map_pow_iff] at hx
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, hy⟩ := exists_sub_algebraMap_mem_map_pow fg n x
    rw [Ideal.map_pow] at hy
    exact ⟨Ideal.Quotient.mk _ y, (Ideal.Quotient.eq.mpr hy).symm⟩

/-- For a finitely generated ideal `I`, the map `R ⧸ I → R̂ ⧸ I R̂` induced by the canonical map
`R → R̂` is bijective: the case `n = 1` of `AdicCompletion.quotientMap_algebraMap_bijective`. -/
theorem quotientMap_algebraMap_bijective_one (fg : I.FG) :
    Function.Bijective (Ideal.quotientMap (I.map (algebraMap R (AdicCompletion I R)))
      (algebraMap R (AdicCompletion I R)) Ideal.le_comap_map) := by
  -- `quotientMap_algebraMap_bijective` is stated for the powers `I ^ n`; here `n = 1`.
  convert quotientMap_algebraMap_bijective fg 1
    (H := by simpa only [pow_one] using Ideal.le_comap_map) using 3 <;> rw [pow_one]

open Topology in
/-- For a finitely generated ideal `I`, the image of `R` is dense in the adic completion for the
adic topology of the extension of `I`. -/
theorem denseRange_algebraMap [TopologicalSpace (AdicCompletion I R)] (fg : I.FG)
    (hI : IsAdic (I.map (algebraMap R (AdicCompletion I R)))) :
    DenseRange (algebraMap R (AdicCompletion I R)) := by
  refine fun x ↦ mem_closure_iff_nhds.mpr fun U hU ↦ ?_
  obtain ⟨n, -, hn⟩ := (hI.hasBasis_nhds x).mem_iff.mp hU
  obtain ⟨y, hy⟩ := exists_sub_algebraMap_mem_map_pow fg n x
  rw [Ideal.map_pow] at hy
  refine ⟨_, hn ⟨_, neg_mem hy, ?_⟩, y, rfl⟩
  simp only [neg_sub, add_sub_cancel]

/-- The completion of an `I`-adically Hausdorff ring has the exponential characteristic of the
ring, since the ring embeds into it. -/
instance expChar [IsHausdorff I R] (p : ℕ) [ExpChar R p] :
    ExpChar (AdicCompletion I R) p :=
  expChar_of_injective_algebraMap (of_injective I R) p

end AdicCompletion
