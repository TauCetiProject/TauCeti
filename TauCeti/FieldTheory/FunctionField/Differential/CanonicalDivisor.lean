/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Dimension
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Uniqueness

/-!
# The divisor of a Weil differential, and the Riemann–Roch theorem

`TauCeti.Divisor.IsRiemannRochDivisor` records what it means for a divisor `W` to satisfy the
Riemann–Roch identity `ℓ(D) = deg D + 1 - g₀ + ℓ(W - D)`, and everything about such a `W` —
that `g₀` is the genus, that `deg W = 2g - 2` and `ℓ(W) = g`, that any two are linearly
equivalent — is proved there.  What is missing, and is supplied here, is that **one exists**.
That is the Riemann–Roch theorem.

The witness is the divisor of a nonzero Weil differential.  Enlarging a divisor shrinks the space
`Ω_F(D)` of Weil differentials it bounds, so the divisors bounding a fixed `ω` form a downward
closed family; the two facts that make it have a *greatest* element are that the family is stable
under suprema (`TauCeti.mem_weilDifferentialFiltration_sup`) and that its degrees are bounded
above, because past the threshold of Riemann's theorem the index of specialty vanishes and with
it `Ω_F(D)`.
A divisor of maximal degree in the family is then the greatest, since places have positive degree.

Writing `W` for that greatest divisor, multiplication by a function is an injective `k`-linear map
`F → Ω_F` carrying `L(W - D)` onto `Ω_F(D)`: a nonzero `x` has `x · ω ∈ Ω_F(D)` exactly when
`ω ∈ Ω_F(D - div x)`, which by maximality says `D - div x ≤ W`, that is `x ∈ L(W - D)`; and it is
onto because every Weil differential is a multiple of `ω` (Proposition 1.5.9, already available as
`TauCeti.exists_repartitionDualMul_eq`).  So `ℓ(W - D) = dim_k Ω_F(D) = i(D)`, which rearranges to
the Riemann–Roch identity.

## Main definitions

* `TauCeti.weilDifferentialDivisor`: **the divisor `(ω)` of a nonzero Weil differential**
  (Stichtenoth, Definition 1.5.11), the greatest divisor bounding it.
* `TauCeti.canonicalClass`: **the canonical class** in the divisor class group, represented by
  the divisor of any nonzero Weil differential.
* `TauCeti.riemannRochSpaceEquivWeilDifferentialFiltration`: **the duality isomorphism**
  `L(W - D) ≃ Ω_F(D)`, `x ↦ x · ω` (Stichtenoth, Theorem 1.5.14).

## Main results

* `TauCeti.exists_forall_degree_lt_of_mem_weilDifferentialFiltration`: the divisors bounding a
  fixed nonzero Weil differential have bounded degree.
* `TauCeti.exists_isGreatest_mem_weilDifferentialFiltration`: **the divisor of a nonzero Weil
  differential** — among the divisors bounding it there is a greatest (Stichtenoth,
  Proposition 1.5.11).
* `TauCeti.mem_weilDifferentialFiltration_iff_le_of_isGreatest` and
  `TauCeti.mem_weilDifferentialFiltration_iff_le_weilDifferentialDivisor`: `ω ∈ Ω_F(D) ↔ D ≤ (ω)`,
  the characteristic property of that divisor.
* `TauCeti.weilDifferentialDivisor_repartitionDualMul`: **the transformation law**
  `(z · ω) = div z + (ω)` (Stichtenoth, Proposition 1.5.13), which is what makes the class of
  `(ω)` — the canonical class — independent of `ω`.
* `TauCeti.divisorClass_weilDifferentialDivisor`: the divisor of every nonzero Weil differential
  represents `TauCeti.canonicalClass`.
* `TauCeti.repartitionDualMul_mem_weilDifferentialFiltration_iff_mem_riemannRochSpace`: the
  membership `x · ω ∈ Ω_F(D) ↔ x ∈ L(W - D)` that carries the theorem.
* `TauCeti.map_riemannRochSpace_repartitionDualMulRight` and
  `TauCeti.dim_sub_eq_finrank_weilDifferentialFiltration`: **the duality theorem** — `x ↦ x · ω`
  maps `L(W - D)` onto `Ω_F(D)`, so `ℓ(W - D) = dim_k Ω_F(D)` (Stichtenoth, Theorem 1.5.14).
* `TauCeti.isRiemannRochDivisor_of_isGreatest_mem_weilDifferentialFiltration`: that divisor is a
  Riemann–Roch divisor for the genus (Stichtenoth, Theorem 1.5.15).
* `TauCeti.exists_isRiemannRochDivisor`: **the Riemann–Roch theorem** — a Riemann–Roch divisor
  exists.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5, in particular Proposition 1.5.11, Theorem 1.5.14 and Theorem 1.5.15.
-/

public section

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-! ### The divisor of a nonzero Weil differential -/

/-- The divisors bounding a fixed nonzero Weil differential have bounded degree: past the
threshold of `TauCeti.exists_forall_indexOfSpecialty_eq_zero` the divisor is nonspecial, and a
nonspecial divisor bounds no nonzero Weil differential. -/
theorem exists_forall_degree_lt_of_mem_weilDifferentialFiltration (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ≠ 0) :
    ∃ c : ℤ, ∀ D : Divisor k F, ω ∈ weilDifferentialFiltration D → Divisor.degree D < c := by
  obtain ⟨c, hc⟩ := exists_forall_indexOfSpecialty_eq_zero hF hex
  refine ⟨c, fun D hD ↦ ?_⟩
  by_contra hcon
  push Not at hcon
  have hbot : weilDifferentialFiltration D = ⊥ :=
    (weilDifferentialFiltration_eq_bot_iff_indexOfSpecialty_eq_zero hF hex D).2 (hc D hcon)
  exact hω (by simpa [hbot] using hD)

/-- **The divisor of a nonzero Weil differential** (Stichtenoth, Proposition 1.5.11): the
divisors bounding `ω` have a greatest element.

Degrees are bounded above, so a divisor `W` of maximal degree among them exists; for any other
`D` bounding `ω`, the supremum `D ⊔ W` also bounds `ω` and has degree at least that of `W` by
monotonicity and at most by maximality, hence equals `W` because places have positive degree. -/
theorem exists_isGreatest_mem_weilDifferentialFiltration (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hmem : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0) :
    ∃ W : Divisor k F, IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W := by
  classical
  obtain ⟨c, hc⟩ := exists_forall_degree_lt_of_mem_weilDifferentialFiltration hF hex hω
  obtain ⟨D₀, hD₀⟩ := mem_weilDifferentialSpace_iff.mp hmem
  obtain ⟨m, ⟨W, hWmem, hWdeg⟩, hmax⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun n : ℤ ↦ ∃ D : Divisor k F, ω ∈ weilDifferentialFiltration D ∧
        Divisor.degree D = n)
      ⟨c, fun n ⟨D, hD, hDn⟩ ↦ hDn ▸ (hc D hD).le⟩
      ⟨Divisor.degree D₀, D₀, hD₀, rfl⟩
  refine ⟨W, hWmem, fun D hD ↦ ?_⟩
  have hsup : ω ∈ weilDifferentialFiltration (D ⊔ W) := mem_weilDifferentialFiltration_sup hD hWmem
  have hle : Divisor.degree (D ⊔ W) ≤ Divisor.degree W := hWdeg ▸ hmax _ ⟨D ⊔ W, hsup, rfl⟩
  have hge : Divisor.degree W ≤ Divisor.degree (D ⊔ W) := Divisor.degree_le_of_le le_sup_right
  have hWeq : W = D ⊔ W := Divisor.eq_of_le_of_degree_eq hF le_sup_right (le_antisymm hge hle)
  exact hWeq ▸ le_sup_left

/-- The characteristic property of the divisor of `ω`, in the form consumers use: `ω` is bounded
by `D` exactly when `D` is at most the divisor of `ω`.  The forward direction is maximality; the
reverse is antitonicity of the filtration. -/
theorem mem_weilDifferentialFiltration_iff_le_of_isGreatest
    {ω : Module.Dual k ↥(repartitionSpace k F)} {W : Divisor k F}
    (hW : IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W) (D : Divisor k F) :
    ω ∈ weilDifferentialFiltration D ↔ D ≤ W :=
  ⟨fun h ↦ hW.2 h, fun h ↦ weilDifferentialFiltration_antitone h hW.1⟩

/-- **The divisor `(ω)` of a nonzero Weil differential** (Stichtenoth, Definition 1.5.11): the
greatest divisor bounding `ω`, which exists by
`TauCeti.exists_isGreatest_mem_weilDifferentialFiltration`.  The hypotheses are exactly what that
existence needs, so the value is always the divisor it is meant to denote; its characteristic
property is `TauCeti.mem_weilDifferentialFiltration_iff_le_weilDifferentialDivisor`. -/
noncomputable def weilDifferentialDivisor (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hmem : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0) : Divisor k F :=
  (exists_isGreatest_mem_weilDifferentialFiltration hF hex hmem hω).choose

/-- The divisor of a nonzero Weil differential is indeed the greatest divisor bounding it. -/
theorem isGreatest_weilDifferentialDivisor (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hmem : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0) :
    IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D}
      (weilDifferentialDivisor hF hex hmem hω) :=
  (exists_isGreatest_mem_weilDifferentialFiltration hF hex hmem hω).choose_spec

/-- **The characteristic property of `(ω)`**: a nonzero Weil differential is bounded by `D`
exactly when `D ≤ (ω)`. -/
@[simp]
theorem mem_weilDifferentialFiltration_iff_le_weilDifferentialDivisor (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hmem : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0) (D : Divisor k F) :
    ω ∈ weilDifferentialFiltration D ↔ D ≤ weilDifferentialDivisor hF hex hmem hω :=
  mem_weilDifferentialFiltration_iff_le_of_isGreatest
    (isGreatest_weilDifferentialDivisor hF hex hmem hω) D

/-- **The transformation law `(z · ω) = div z + (ω)`** (Stichtenoth, Proposition 1.5.13): the
divisor of a Weil differential changes by a principal divisor when the differential is multiplied
by a nonzero function, so the class of `(ω)` in the divisor class group — the canonical class —
does not depend on `ω`.

Multiplication translates the filtration by `div z`
(`TauCeti.repartitionDualMul_mem_weilDifferentialFiltration_iff`), so it carries the divisors
bounding `ω` bijectively onto those bounding `z · ω`, hence greatest element to greatest
element. -/
theorem weilDifferentialDivisor_repartitionDualMul (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hmem : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0) (z : Fˣ)
    (hzmem : repartitionDualMul hF (z : F) ω ∈ weilDifferentialSpace k F)
    (hz : repartitionDualMul hF (z : F) ω ≠ 0) :
    weilDifferentialDivisor hF hex hzmem hz =
      Divisor.principal hF z + weilDifferentialDivisor hF hex hmem hω := by
  have hW := isGreatest_weilDifferentialDivisor hF hex hmem hω
  refine (isGreatest_weilDifferentialDivisor hF hex hzmem hz).unique ⟨?_, fun D hD ↦ ?_⟩
  · have h := (repartitionDualMul_mem_weilDifferentialFiltration_iff hF z
      (D := weilDifferentialDivisor hF hex hmem hω) (ω := ω)).mpr hW.1
    rwa [add_comm] at h
  · have h := (repartitionDualMul_mem_weilDifferentialFiltration_iff hF z⁻¹
      (D := D) (ω := repartitionDualMul hF (z : F) ω)).mpr hD
    have hcancel : repartitionDualMul hF ((z⁻¹ : Fˣ) : F) (repartitionDualMul hF (z : F) ω) = ω :=
      by simp
    rw [hcancel, Divisor.principal_inv, ← sub_eq_add_neg] at h
    rw [add_comm]
    exact sub_le_iff_le_add.mp (hW.2 h)

/-- The divisors of any two nonzero Weil differentials have the same divisor class.  Indeed,
one differential is a nonzero function multiple of the other, and the transformation law says
that their divisors differ by the corresponding principal divisor. -/
theorem divisorClass_weilDifferentialDivisor_eq (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω η : Module.Dual k ↥(repartitionSpace k F)}
    (hωmem : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0)
    (hηmem : η ∈ weilDifferentialSpace k F) (hη : η ≠ 0) :
    (Place.orderSystem hF).divisorClass (weilDifferentialDivisor hF hex hωmem hω) =
      (Place.orderSystem hF).divisorClass (weilDifferentialDivisor hF hex hηmem hη) := by
  obtain ⟨c, hc⟩ := exists_repartitionDualMul_eq hF hex hωmem hω hηmem
  subst hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hη (by simp)
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, (z : F) = c := ⟨Units.mk0 c hc0, rfl⟩
  rw [weilDifferentialDivisor_repartitionDualMul hF hex hωmem hω z hηmem hη, map_add,
    (Divisor.divisorClass_eq_zero_iff hF).mpr ⟨z, rfl⟩, zero_add]

/-- **The canonical class** of an algebraic function field with exact constant field: the divisor
class of a nonzero Weil differential.  Such a differential exists by
`TauCeti.weilDifferentialSpace_ne_bot`, and
`TauCeti.divisorClass_weilDifferentialDivisor` shows that the class is independent of the chosen
differential. -/
noncomputable def canonicalClass (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) : (Place.orderSystem hF).ClassGroup :=
  (Place.orderSystem hF).divisorClass
    (weilDifferentialDivisor hF hex
      ((Submodule.ne_bot_iff _).mp (weilDifferentialSpace_ne_bot hF hex)).choose_spec.1
      ((Submodule.ne_bot_iff _).mp (weilDifferentialSpace_ne_bot hF hex)).choose_spec.2)

/-- Every nonzero Weil differential represents the canonical class. -/
theorem divisorClass_weilDifferentialDivisor (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hmem : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0) :
    (Place.orderSystem hF).divisorClass (weilDifferentialDivisor hF hex hmem hω) =
      canonicalClass hF hex := by
  unfold canonicalClass
  exact divisorClass_weilDifferentialDivisor_eq hF hex hmem hω _ _

/-! ### The Riemann–Roch theorem -/

/-- **Duality between `L(W - D)` and `Ω_F(D)`**, for `W` the divisor of `ω`: a function `x`
multiplies `ω` into `Ω_F(D)` exactly when it lies in `L(W - D)`.

For nonzero `x`, multiplication translates the filtration by the principal divisor of `x`
(`TauCeti.repartitionDualMul_mem_weilDifferentialFiltration_iff`), so `x · ω ∈ Ω_F(D)` says
`ω ∈ Ω_F(D - div x)`, which by maximality of `W` says `D - div x ≤ W`. -/
theorem repartitionDualMul_mem_weilDifferentialFiltration_iff_mem_riemannRochSpace
    (hF : IsFunctionField k F) {ω : Module.Dual k ↥(repartitionSpace k F)} {W : Divisor k F}
    (hW : IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W)
    (D : Divisor k F) (x : F) :
    repartitionDualMul hF x ω ∈ weilDifferentialFiltration D ↔ x ∈ riemannRochSpace (W - D) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, (z : F) = x := ⟨Units.mk0 x hx, rfl⟩
  have habel : W - (D - Divisor.principal hF z) = Divisor.principal hF z + (W - D) := by abel
  have hrw : D - Divisor.principal hF z + Divisor.principal hF z = D := by abel
  have hiff : (D - Divisor.principal hF z ≤ W) ↔ 0 ≤ Divisor.principal hF z + (W - D) := by
    rw [← habel]; exact sub_nonneg.symm
  rw [mem_riemannRochSpace_units_iff hF, ← hiff]
  constructor
  · intro h
    refine hW.2 ((repartitionDualMul_mem_weilDifferentialFiltration_iff hF z).mp ?_)
    rwa [hrw]
  · intro h
    have hmem := (repartitionDualMul_mem_weilDifferentialFiltration_iff hF z).mpr
      (weilDifferentialFiltration_antitone h hW.1)
    rwa [hrw] at hmem

/-- **The image of `L(W - D)` under multiplication by `ω` is `Ω_F(D)`.**  One inclusion is
`TauCeti.repartitionDualMul_mem_weilDifferentialFiltration_iff_mem_riemannRochSpace`; the other
is Proposition 1.5.9, every Weil differential being a multiple of `ω`
(`TauCeti.exists_repartitionDualMul_eq`). -/
theorem map_riemannRochSpace_repartitionDualMulRight (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ≠ 0)
    {W : Divisor k F}
    (hW : IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W) (D : Divisor k F) :
    Submodule.map (repartitionDualMulRight hF ω) (riemannRochSpace (W - D)) =
      weilDifferentialFiltration D := by
  have key (x : F) : repartitionDualMulRight hF ω x ∈ weilDifferentialFiltration D ↔
      x ∈ riemannRochSpace (W - D) := by
    simpa using repartitionDualMul_mem_weilDifferentialFiltration_iff_mem_riemannRochSpace hF hW D x
  refine le_antisymm ?_ fun η hη ↦ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (key x).mpr hx
  · obtain ⟨c, hc⟩ := exists_repartitionDualMul_eq hF hex
      (weilDifferentialFiltration_le_weilDifferentialSpace W hW.1) hω
      (weilDifferentialFiltration_le_weilDifferentialSpace D hη)
    exact ⟨c, (key c).mp (by simpa [hc] using hη), by simpa using hc⟩

/-- **The duality theorem** (Stichtenoth, Theorem 1.5.14): for `W` the divisor of a nonzero Weil
differential `ω`, multiplication by `ω` is a `k`-linear isomorphism `L(W - D) ≃ Ω_F(D)`.  It is
injective by `TauCeti.repartitionDualMulRight_injective` and onto by
`TauCeti.map_riemannRochSpace_repartitionDualMulRight`. -/
noncomputable def riemannRochSpaceEquivWeilDifferentialFiltration (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ≠ 0)
    {W : Divisor k F}
    (hW : IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W) (D : Divisor k F) :
    ↥(riemannRochSpace (W - D)) ≃ₗ[k] ↥(weilDifferentialFiltration D) :=
  (Submodule.equivMapOfInjective _ (repartitionDualMulRight_injective hF hω)
    (riemannRochSpace (W - D))).trans
      (LinearEquiv.ofEq _ _ (map_riemannRochSpace_repartitionDualMulRight hF hex hω hW D))

/-- The duality equivalence sends `x` to the Weil differential `x · ω`. -/
@[simp]
theorem riemannRochSpaceEquivWeilDifferentialFiltration_apply (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ≠ 0)
    {W : Divisor k F}
    (hW : IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W) (D : Divisor k F)
    (x : ↥(riemannRochSpace (W - D))) :
    (riemannRochSpaceEquivWeilDifferentialFiltration hF hex hω hW D x :
      Module.Dual k ↥(repartitionSpace k F)) = repartitionDualMul hF x ω := by
  rw [riemannRochSpaceEquivWeilDifferentialFiltration, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, Submodule.coe_equivMapOfInjective_apply,
    repartitionDualMulRight_apply]

/-- **The duality theorem, in dimensions**: `ℓ(W - D) = dim_k Ω_F(D)`. -/
theorem dim_sub_eq_finrank_weilDifferentialFiltration (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ≠ 0)
    {W : Divisor k F}
    (hW : IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W) (D : Divisor k F) :
    Divisor.dim (W - D) = Module.finrank k ↥(weilDifferentialFiltration D) := by
  rw [Divisor.dim_def]
  exact (riemannRochSpaceEquivWeilDifferentialFiltration hF hex hω hW D).finrank_eq

/-- **The Riemann–Roch theorem** (Stichtenoth, Theorem 1.5.15): the divisor of a nonzero Weil
differential is a Riemann–Roch divisor for the genus.

Duality gives `ℓ(W - D) = dim_k Ω_F(D)`, which is `i(D)` by
`TauCeti.finrank_weilDifferentialFiltration` (Lemma 1.5.7); unfolding the index of specialty
rearranges that to the Riemann–Roch identity. -/
theorem isRiemannRochDivisor_of_isGreatest_mem_weilDifferentialFiltration
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ≠ 0) {W : Divisor k F}
    (hW : IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W) :
    W.IsRiemannRochDivisor (genus k F) := by
  rw [Divisor.isRiemannRochDivisor_iff]
  intro D
  have hi := finrank_weilDifferentialFiltration hF hex D
  rw [← dim_sub_eq_finrank_weilDifferentialFiltration hF hex hω hW D,
    Divisor.indexOfSpecialty_def] at hi
  omega

/-- **The Riemann–Roch theorem, existence form** (Stichtenoth, Theorem 1.5.15 with
Corollary 1.5.16): every algebraic function field with exact constant field has a Riemann–Roch
divisor, namely the divisor of any nonzero Weil differential.  With
`TauCeti.Divisor.IsRiemannRochDivisor.dim_eq` and
`TauCeti.Divisor.IsRiemannRochDivisor.degree_eq` this gives `ℓ(W) = g` and `deg W = 2g - 2`, and
with `TauCeti.Divisor.IsRiemannRochDivisor.linearlyEquivalent` the class of `W` — the canonical
class — is well defined. -/
theorem exists_isRiemannRochDivisor (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) :
    ∃ W : Divisor k F, W.IsRiemannRochDivisor (genus k F) := by
  obtain ⟨ω, hωmem, hω0⟩ := (Submodule.ne_bot_iff _).mp (weilDifferentialSpace_ne_bot hF hex)
  exact ⟨weilDifferentialDivisor hF hex hωmem hω0,
    isRiemannRochDivisor_of_isGreatest_mem_weilDifferentialFiltration hF hex hω0
      (isGreatest_weilDifferentialDivisor hF hex hωmem hω0)⟩

end TauCeti
