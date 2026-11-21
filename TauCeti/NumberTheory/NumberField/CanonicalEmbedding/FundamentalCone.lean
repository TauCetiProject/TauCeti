/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.UnitAction
import TauCeti.RingTheory.ClassGroup.Basic

/-!
# Unit orbits and fundamental-cone points of ideal lattices

Let `I` be an invertible fractional ideal of a number field `K`. Every nonzero ideal `𝔟` of `𝓞 K`
in the inverse ideal class `[I]⁻¹` has `𝔟 * I` principal, with a generator whose image under
`mixedEmbedding K` lies in Mathlib's `NumberField.mixedEmbedding.fundamentalCone K`; since the cone
is a fundamental domain for the units of `𝓞 K` modulo torsion, each such `𝔟` contributes one
`(𝓞 K)ˣ`-orbit of nonzero lattice points and `w = #μ(K)` points in the cone. Mathlib records the
integral-ideal cone correspondence fibre by fibre of the norm
(`NumberField.mixedEmbedding.fundamentalCone.idealSetEquivNorm`).

This file records the norm-unrestricted unit-orbit and fundamental-cone parametrizations for the
lattice `idealLattice K I` of any invertible fractional ideal `I`, together with the bridge to
Mathlib's `idealSet K J` for a nonzero integral ideal `J`:

* `coneGen I 𝔟`: for a nonzero integral ideal `𝔟` of class `(ClassGroup.mk K I)⁻¹`, a chosen
  nonzero generator of `𝔟 * I` lying in `I` whose canonical embedding lies in `fundamentalCone K`.
* `idealLatticeNeZeroEquiv I`: bijection between `{𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 =
  (ClassGroup.mk K I)⁻¹} × (𝓞 K)ˣ` and `{x : idealLattice K I // x ≠ 0}` parametrizing the nonzero
  points of `σ(I)` by unit orbits of cone generators.
* `idealLatticeFundamentalConeEquiv I`: bijection between `{𝔟 : (Ideal (𝓞 K))⁰ //
  ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} × torsion K` and `{x : idealLattice K I //
  (x : mixedSpace K) ∈ fundamentalCone K}` parametrizing the fundamental-cone points of `σ(I)`.
* `idealSetEquivIdealLatticeFundamentalCone K J`: identification of `idealSet K J` with the
  fundamental-cone points of `idealLattice K (FractionalIdeal.mk0 K J)`.

## Main declarations

* `NumberField.mixedEmbedding.fundamentalCone.coneGen`,
  `NumberField.mixedEmbedding.fundamentalCone.idealLatticeNeZeroEquiv`,
  `NumberField.mixedEmbedding.fundamentalCone.idealLatticeFundamentalConeEquiv`,
  `NumberField.mixedEmbedding.fundamentalCone.idealSetEquivIdealLatticeFundamentalCone`.
* `NumberField.mixedEmbedding.fundamentalCone.natCard_unitSMul_eq_torsionOrder`: a point of
  nonzero norm is `u • a`, with `a` a point of the cone and `u` a unit, for exactly `w` pairs
  `(a, u)`.
* `NumberField.mixedEmbedding.fundamentalCone.interIdealLatticeEquiv`: scaling by a nonzero
  rational `q` with `I₂ = (q) * I₁` maps `fundamentalCone K ∩ idealLattice K I₁` bijectively onto
  `fundamentalCone K ∩ idealLattice K I₂`.
* `NumberField.mixedEmbedding.fundamentalCone.coneOrbitEquiv`: choosing coset representatives
  identifies `(fundamentalCone K ∩ idealLattice K I) × ((𝓞 K)ˣ ⧸ torsion K)` bijectively with the
  nonzero points of `idealLattice K I`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, (5.3).
-/

public section

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units Ideal Submodule
open scoped nonZeroDivisors

namespace NumberField.mixedEmbedding.fundamentalCone

variable {K : Type*} [Field K] [NumberField K] {J : (Ideal (𝓞 K))⁰}

/-- `idealSet K J` is canonically equivalent to the subtype of points of
`idealLattice K (FractionalIdeal.mk0 K J)` lying in `fundamentalCone K`. -/
noncomputable def idealSetEquivIdealLatticeFundamentalCone (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) :
    idealSet K J ≃
      {x : idealLattice K (FractionalIdeal.mk0 K J) // (x : mixedSpace K) ∈ fundamentalCone K} :=
  (Equiv.subtypeEquivRight fun x ↦ by
    rw [idealSet, Set.mem_inter_iff, SetLike.mem_coe, and_comm]).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun x : mixedSpace K ↦ x ∈ idealLattice K (FractionalIdeal.mk0 K J))
      (fun x : mixedSpace K ↦ x ∈ fundamentalCone K)).symm

/-- `idealSetEquivIdealLatticeFundamentalCone` preserves the underlying point of `mixedSpace K`. -/
@[simp]
theorem coe_idealSetEquivIdealLatticeFundamentalCone (a : idealSet K J) :
    ((idealSetEquivIdealLatticeFundamentalCone K J a :
        idealLattice K (FractionalIdeal.mk0 K J)) : mixedSpace K) = a :=
  (rfl)

/-! ### Unit-orbit parametrization of a fractional-ideal lattice -/

/-- Every nonzero integral ideal `𝔟` in the inverse class `[I]⁻¹` admits a nonzero generator `a` of
`𝔟 * I` lying in `I` whose canonical embedding lies in `fundamentalCone K`. -/
theorem exists_coneGen (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹}) :
    ∃ a : K, a ≠ 0 ∧ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K) ∧
      (𝔟.val.val : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ a ∧
      mixedEmbedding K a ∈ fundamentalCone K := by
  obtain ⟨x, hx⟩ := (ClassGroup.mk0_eq_inv_mk_iff I 𝔟.val).mp 𝔟.property
  have hx_norm : mixedEmbedding.norm (mixedEmbedding K (x : K)) ≠ 0 := by
    rw [norm_eq_norm, ne_eq, Rat.cast_eq_zero, abs_eq_zero, Algebra.norm_eq_zero_iff]
    exact x.ne_zero
  obtain ⟨u, hu⟩ := exists_unit_smul_mem hx_norm
  have hspan : (𝔟.val.val : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (u • (x : K)) := by
    rw [hx, ← FractionalIdeal.spanSingleton_units_smul u (x : K)]
  have hu0 : u • (x : K) ≠ 0 := by
    rw [Units.smul_def, Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap]
    exact mul_ne_zero (Units.coe_ne_zero u) x.ne_zero
  refine ⟨u • (x : K), hu0, ?_, hspan, ?_⟩
  · exact FractionalIdeal.spanSingleton_le_iff_mem.mp
      (hspan ▸ mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one)
  · rwa [mixedEmbedding_units_smul]

/-- For `𝔟` in `[I]⁻¹`, a chosen nonzero generator of `𝔟 * I` in `I` whose canonical embedding lies
in `fundamentalCone K`. -/
noncomputable def coneGen (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹}) : K :=
  (exists_coneGen I 𝔟).choose

/-- `coneGen I 𝔟` is nonzero. -/
theorem coneGen_ne_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹}) :
    coneGen I 𝔟 ≠ 0 :=
  (exists_coneGen I 𝔟).choose_spec.1

/-- `coneGen I 𝔟` belongs to `I`. -/
theorem coneGen_mem (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹}) :
    coneGen I 𝔟 ∈ (I : FractionalIdeal (𝓞 K)⁰ K) :=
  (exists_coneGen I 𝔟).choose_spec.2.1

/-- `𝔟 * I` is the principal fractional ideal generated by `coneGen I 𝔟`. -/
theorem mul_eq_spanSingleton_coneGen (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹}) :
    (𝔟.val.val : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (coneGen I 𝔟) :=
  (exists_coneGen I 𝔟).choose_spec.2.2.1

/-- The canonical embedding of `coneGen I 𝔟` lies in `fundamentalCone K`. -/
theorem mixedEmbedding_coneGen_mem (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹}) :
    mixedEmbedding K (coneGen I 𝔟) ∈ fundamentalCone K :=
  (exists_coneGen I 𝔟).choose_spec.2.2.2

/-- The mixed norm of `mixedEmbedding K (coneGen I 𝔟)` is `N(𝔟) * N(I)`. -/
theorem norm_mixedEmbedding_coneGen (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹}) :
    mixedEmbedding.norm (mixedEmbedding K (coneGen I 𝔟)) =
      (Ideal.absNorm (𝔟.val : Ideal (𝓞 K)) : ℝ) *
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  have hq : |Algebra.norm ℚ (coneGen I 𝔟)| =
      FractionalIdeal.absNorm ((𝔟.val.val : FractionalIdeal (𝓞 K)⁰ K) * I.val) := by
    rw [mul_eq_spanSingleton_coneGen, FractionalIdeal.absNorm_span_singleton]
  rw [norm_eq_norm, hq, map_mul, FractionalIdeal.coeIdeal_absNorm, Rat.cast_mul, Rat.cast_natCast]

/-- Every nonzero element `a ∈ I` is a unit multiple `u • coneGen I 𝔟` for some `𝔟` in `[I]⁻¹`. -/
theorem exists_unit_smul_coneGen_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {a : K}
    (ha : a ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) (ha0 : a ≠ 0) :
    ∃ 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
      ∃ u : (𝓞 K)ˣ, u • coneGen I 𝔟 = a := by
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ a * ↑I⁻¹ ≤ 1 := by
    calc FractionalIdeal.spanSingleton (𝓞 K)⁰ a * ↑I⁻¹
        ≤ I.val * ↑I⁻¹ := mul_left_mono (FractionalIdeal.spanSingleton_le_iff_mem.mpr ha)
      _ = 1 := Units.mul_inv I
  obtain ⟨𝔟₀, h𝔟₀⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hmul : (𝔟₀ : FractionalIdeal (𝓞 K)⁰ K) * I.val =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
    rw [h𝔟₀, mul_assoc, Units.inv_mul, mul_one]
  have h𝔟₀_ne : 𝔟₀ ≠ ⊥ := by
    rintro rfl
    simp at hmul
    exact ha0 (FractionalIdeal.spanSingleton_eq_zero_iff.mp hmul.symm)
  let 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} :=
    ⟨⟨𝔟₀, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔟₀_ne⟩,
      (ClassGroup.mk0_eq_inv_mk_iff I _).mpr ⟨Units.mk0 a ha0, hmul⟩⟩
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (coneGen I 𝔟) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
    rw [← mul_eq_spanSingleton_coneGen, ← hmul]
  exact ⟨𝔟, FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan⟩

/-- **Unit-orbit parametrization of `idealLattice K I`.** Bijection between pairs `(𝔟, u)` with
`𝔟` in `[I]⁻¹` and `u : (𝓞 K)ˣ` and the nonzero points of `idealLattice K I`. -/
noncomputable def idealLatticeNeZeroEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} × (𝓞 K)ˣ ≃
      {x : idealLattice K I // x ≠ 0} := by
  refine Equiv.ofBijective (fun p ↦ ⟨⟨p.2 • mixedEmbedding K (coneGen I p.1),
      (p.2.unitSMul_mem_idealLattice_iff I _).mpr
        ((mem_idealLattice K I).mpr ⟨coneGen I p.1, coneGen_mem I p.1, rfl⟩)⟩, ?_⟩) ⟨?_, ?_⟩
  · intro h0
    have h1 : p.2 • mixedEmbedding K (coneGen I p.1) = 0 := (Submodule.mk_eq_zero _ _).mp h0
    rw [unit_smul_eq_zero, map_eq_zero_iff _ (mixedEmbedding_injective K)] at h1
    exact coneGen_ne_zero I p.1 h1
  · rintro ⟨𝔟₁, u₁⟩ ⟨𝔟₂, u₂⟩ h
    have heq : u₁ • coneGen I 𝔟₁ = u₂ • coneGen I 𝔟₂ := by
      apply mixedEmbedding_injective K
      simpa only [Subtype.ext_iff, ← mixedEmbedding_units_smul] using h
    have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (coneGen I 𝔟₁) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (coneGen I 𝔟₂) := by
      simpa only [FractionalIdeal.spanSingleton_units_smul] using
        congrArg (FractionalIdeal.spanSingleton (𝓞 K)⁰) heq
    have h𝔟 : 𝔟₁ = 𝔟₂ := by
      apply Subtype.ext
      apply Subtype.ext
      apply FractionalIdeal.coeIdeal_injective (K := K)
      exact mul_right_cancel₀ I.ne_zero
        ((mul_eq_spanSingleton_coneGen I 𝔟₁).trans
          (hspan.trans (mul_eq_spanSingleton_coneGen I 𝔟₂).symm))
    subst h𝔟
    simp only [Units.smul_def, Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap] at heq
    have hu : (u₁ : K) = (u₂ : K) := mul_right_cancel₀ (coneGen_ne_zero I 𝔟₁) heq
    exact Prod.ext rfl (Units.ext (RingOfIntegers.ext hu))
  · rintro ⟨⟨x, hx⟩, hx0⟩
    obtain ⟨a, ha, rfl⟩ := (mem_idealLattice K I).mp hx
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hx0 ((Submodule.mk_eq_zero _ _).mpr (map_zero _))
    obtain ⟨𝔟, u, hu⟩ := exists_unit_smul_coneGen_eq I ha ha0
    refine ⟨(𝔟, u), Subtype.ext (Subtype.ext ?_)⟩
    simp only [← mixedEmbedding_units_smul, hu]

/-- `idealLatticeNeZeroEquiv` sends `(𝔟, u)` to `u • mixedEmbedding K (coneGen I 𝔟)`. -/
@[simp]
theorem coe_idealLatticeNeZeroEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} × (𝓞 K)ˣ) :
    ((idealLatticeNeZeroEquiv I p).val : mixedSpace K) =
      p.2 • mixedEmbedding K (coneGen I p.1) :=
  (rfl)

/-- **Fundamental-cone parametrization of `idealLattice K I`.** Bijection between pairs `(𝔟, ζ)`
with `𝔟` in `[I]⁻¹` and `ζ : Units.torsion K` and the points of `idealLattice K I` lying in
`fundamentalCone K`. -/
noncomputable def idealLatticeFundamentalConeEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} × Units.torsion K ≃
      {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K} where
  toFun p := ⟨(idealLatticeNeZeroEquiv I (p.1, p.2.val)).val, by
    rw [coe_idealLatticeNeZeroEquiv]
    exact (unit_smul_mem_iff_mem_torsion (mixedEmbedding_coneGen_mem I p.1) p.2.val).mpr
        p.2.property⟩
  invFun x :=
    let hx0 : x.val ≠ 0 := fun h0 ↦ by
      have := norm_pos_of_mem (K := K) x.property
      rw [h0, Submodule.coe_zero, map_zero] at this
      exact lt_irrefl 0 this
    let q := (idealLatticeNeZeroEquiv I).symm ⟨x.val, hx0⟩
    (q.1, ⟨q.2, (unit_smul_mem_iff_mem_torsion (mixedEmbedding_coneGen_mem I q.1) q.2).mp <| by
      rw [← coe_idealLatticeNeZeroEquiv I q, (idealLatticeNeZeroEquiv I).apply_symm_apply]
      exact x.property⟩)
  left_inv p := by
    dsimp only
    simp only [Subtype.coe_eta, Equiv.symm_apply_apply, Prod.mk.eta]
  right_inv x := by
    dsimp only
    simp only [Prod.mk.eta, Equiv.apply_symm_apply, Subtype.coe_eta]

/-- `idealLatticeFundamentalConeEquiv` sends `(𝔟, ζ)` to `ζ • mixedEmbedding K (coneGen I 𝔟)`. -/
@[simp]
theorem coe_idealLatticeFundamentalConeEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} × Units.torsion K) :
    ((idealLatticeFundamentalConeEquiv I p : idealLattice K I) : mixedSpace K) =
      (p.2 : (𝓞 K)ˣ) • mixedEmbedding K (coneGen I p.1) := by
  simp only [idealLatticeFundamentalConeEquiv, Equiv.coe_fn_mk, coe_idealLatticeNeZeroEquiv]

/-- **The unit multiples of the points of the cone.** A point `x` of nonzero norm is `u • a`, with
`a` a point of the fundamental cone and `u` a unit, for exactly `w = #μ(K)` pairs `(a, u)`: the
units `u` with `u⁻¹ • x` in the cone form a coset of the torsion. -/
theorem natCard_unitSMul_eq_torsionOrder {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    Nat.card {p : fundamentalCone K × (𝓞 K)ˣ // p.2 • (p.1 : mixedSpace K) = x} =
      torsionOrder K := by
  obtain ⟨u₁, hu₁⟩ := exists_unit_smul_mem hx
  have hmem (ζ : Units.torsion K) : ((ζ : (𝓞 K)ˣ) * u₁) • x ∈ fundamentalCone K := by
    rw [mul_smul]
    exact torsion_smul_mem_of_mem hu₁ ζ.property
  -- `ζ ↦ ((ζ u₁) x, (ζ u₁)⁻¹)` is a bijection from the torsion onto the pairs
  refine (Nat.card_eq_of_bijective (fun ζ : Units.torsion K ↦
    ⟨(⟨_, hmem ζ⟩, ((ζ : (𝓞 K)ˣ) * u₁)⁻¹), inv_smul_smul _ _⟩)
    ⟨fun ζ ζ' h ↦ ?_, fun ⟨⟨a, u⟩, (hp : u • (a : mixedSpace K) = x)⟩ ↦ ?_⟩).symm
  · simpa using congrArg (fun q ↦ (q.val.2 : (𝓞 K)ˣ)) h
  · have hζ : u⁻¹ * u₁⁻¹ ∈ Units.torsion K := by
      rw [← unit_smul_mem_iff_mem_torsion hu₁, smul_smul, inv_mul_cancel_right, ← hp,
        inv_smul_smul]
      exact a.property
    refine ⟨⟨_, hζ⟩, Subtype.ext (Prod.ext (Subtype.ext ?_) ?_)⟩ <;>
      simp only [inv_mul_cancel_right, ← hp, inv_smul_smul, inv_inv]

/-- Scaling by a nonzero rational `q` with `I₂ = (q) * I₁` maps the fundamental-cone points of
`idealLattice K I₁` bijectively onto those of `idealLattice K I₂`. -/
noncomputable def interIdealLatticeEquiv {I₁ I₂ : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {q : ℚ}
    (hq : q ≠ 0)
    (hI : (I₂ : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (q : K) * (I₁ : FractionalIdeal (𝓞 K)⁰ K)) :
    (fundamentalCone K ∩ idealLattice K I₁ : Set (mixedSpace K)) ≃
      (fundamentalCone K ∩ idealLattice K I₂ : Set (mixedSpace K)) :=
  Equiv.subtypeEquiv (MulAction.toPerm (Units.mk0 (q : ℝ) (Rat.cast_ne_zero.mpr hq))) fun x ↦ by
    have hqR : (q : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hq
    have hq_emb (z : K) : mixedEmbedding K ((q : K) * z) = (q : ℝ) • mixedEmbedding K z := by
      ext w <;> simp [mixedEmbedding, Complex.real_smul]
    simp only [Set.mem_inter_iff, SetLike.mem_coe, MulAction.toPerm_apply,
      Units.smul_def, Units.val_mk0, mem_idealLattice]
    refine and_congr (smul_mem_iff_mem hqR).symm
      ⟨fun ⟨b, hb, hbx⟩ ↦ ⟨(q : K) * b, ?_, ?_⟩, fun ⟨y, hy, hyx⟩ ↦ ?_⟩
    · rw [hI]
      exact FractionalIdeal.mem_singleton_mul.mpr ⟨b, hb, rfl⟩
    · rw [hq_emb, hbx]
    · rw [hI, FractionalIdeal.mem_singleton_mul] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      refine ⟨b, hb, smul_right_injective (mixedSpace K) hqR ?_⟩
      rwa [hq_emb] at hyx

/-- Underlying mixed-space point of `interIdealLatticeEquiv`. -/
@[simp]
theorem interIdealLatticeEquiv_apply_coe {I₁ I₂ : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {q : ℚ}
    (hq : q ≠ 0)
    (hI : (I₂ : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (q : K) * (I₁ : FractionalIdeal (𝓞 K)⁰ K))
    (a : (fundamentalCone K ∩ idealLattice K I₁ : Set (mixedSpace K))) :
    (interIdealLatticeEquiv hq hI a : mixedSpace K) = (q : ℝ) • (a : mixedSpace K) := by
  simp [interIdealLatticeEquiv]

/-- Underlying mixed-space point of `(interIdealLatticeEquiv hq hI).symm`. -/
@[simp]
theorem interIdealLatticeEquiv_symm_apply_coe {I₁ I₂ : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {q : ℚ}
    (hq : q ≠ 0)
    (hI : (I₂ : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (q : K) * (I₁ : FractionalIdeal (𝓞 K)⁰ K))
    (b : (fundamentalCone K ∩ idealLattice K I₂ : Set (mixedSpace K))) :
    ((interIdealLatticeEquiv hq hI).symm b : mixedSpace K) = (q : ℝ)⁻¹ • (b : mixedSpace K) := by
  simp [interIdealLatticeEquiv, Units.smul_def]

/-- Choosing coset representatives `Quotient.out g` identifies
`(fundamentalCone K ∩ idealLattice K I) × ((𝓞 K)ˣ ⧸ Units.torsion K)` bijectively with the nonzero
points of `idealLattice K I`. -/
noncomputable def coneOrbitEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (fundamentalCone K ∩ idealLattice K I : Set (mixedSpace K)) × ((𝓞 K)ˣ ⧸ Units.torsion K) ≃
      {x : idealLattice K I // x ≠ 0} := by
  refine Equiv.ofBijective
    (fun p ↦ ⟨(Quotient.out p.2).unitSMulIdealLatticeEquiv I ⟨p.1.val, p.1.property.2⟩,
      fun h ↦ ?_⟩)
    ⟨?_, ?_⟩
  · have hnorm : mixedEmbedding.norm ((Quotient.out p.2 : (𝓞 K)ˣ) • (p.1 : mixedSpace K)) = 0 := by
      simpa using congrArg (fun z : idealLattice K I ↦ mixedEmbedding.norm (z : mixedSpace K)) h
    rw [norm_unit_smul] at hnorm
    exact (norm_pos_of_mem p.1.property.1).ne' hnorm
  · rintro ⟨a₁, g₁⟩ ⟨a₂, g₂⟩ h
    have hsmul : (Quotient.out g₁ : (𝓞 K)ˣ) • (a₁ : mixedSpace K) =
        (Quotient.out g₂ : (𝓞 K)ˣ) • (a₂ : mixedSpace K) := by
      simpa using congrArg (fun z : {x : idealLattice K I // x ≠ 0} ↦ (z.val : mixedSpace K)) h
    have ha₁ : (a₁ : mixedSpace K) =
        ((Quotient.out g₁)⁻¹ * Quotient.out g₂) • (a₂ : mixedSpace K) := by
      rw [mul_smul, ← hsmul, inv_smul_smul]
    have htor : (Quotient.out g₁)⁻¹ * Quotient.out g₂ ∈ Units.torsion K :=
      (unit_smul_mem_iff_mem_torsion a₂.property.1 _).mp (ha₁ ▸ a₁.property.1)
    have hg : g₁ = g₂ := by
      rw [← Quotient.out_eq g₁, ← Quotient.out_eq g₂]
      exact QuotientGroup.eq.mpr htor
    subst hg
    exact Prod.ext (Subtype.ext (MulAction.injective (Quotient.out g₁) hsmul)) rfl
  · rintro ⟨⟨x, hxI⟩, hx0⟩
    have hx0' : x ≠ 0 := fun h ↦ hx0 (Subtype.ext h)
    obtain ⟨b, -, hb⟩ := (mem_idealLattice K I).mp hxI
    obtain ⟨v, hv⟩ := exists_unit_smul_mem ((norm_eq_zero_iff' ⟨b, hb⟩).not.mpr hx0')
    set g : (𝓞 K)ˣ ⧸ Units.torsion K := QuotientGroup.mk v⁻¹
    set u : (𝓞 K)ˣ := Quotient.out g
    have htor : (v⁻¹)⁻¹ * u ∈ Units.torsion K :=
      QuotientGroup.eq.mp (Quotient.out_eq g).symm
    have htor' : u⁻¹ * v⁻¹ ∈ Units.torsion K := by
      simpa [mul_inv_rev] using Subgroup.inv_mem (Units.torsion K) htor
    have ha_cone : u⁻¹ • x ∈ fundamentalCone K := by
      have heq : u⁻¹ • x = (u⁻¹ * v⁻¹) • (v • x) := by rw [mul_smul, inv_smul_smul]
      rw [heq]
      exact (unit_smul_mem_iff_mem_torsion hv _).mpr htor'
    have haI : u⁻¹ • x ∈ idealLattice K I := (u⁻¹.unitSMul_mem_idealLattice_iff I x).mpr hxI
    refine ⟨(⟨u⁻¹ • x, ha_cone, haI⟩, g), Subtype.ext (Subtype.ext ?_)⟩
    rw [Units.unitSMulIdealLatticeEquiv_apply]
    exact smul_inv_smul u x

/-- Underlying mixed-space point of `coneOrbitEquiv`. -/
@[simp]
theorem coneOrbitEquiv_apply_coe (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : (fundamentalCone K ∩ idealLattice K I : Set (mixedSpace K)))
    (g : (𝓞 K)ˣ ⧸ Units.torsion K) :
    ((coneOrbitEquiv I (a, g) : {x : idealLattice K I // x ≠ 0}) : mixedSpace K) =
      (Quotient.out g : (𝓞 K)ˣ) • (a : mixedSpace K) :=
  Units.unitSMulIdealLatticeEquiv_apply _ _ _

end NumberField.mixedEmbedding.fundamentalCone
