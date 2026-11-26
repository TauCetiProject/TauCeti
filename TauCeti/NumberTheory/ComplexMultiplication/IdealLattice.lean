/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Endomorphism
public import TauCeti.NumberTheory.NumberField.Global.Orders.IdealClassMonoid
public import TauCeti.NumberTheory.NumberField.Global.Orders.Lattice
public import TauCeti.NumberTheory.NumberField.ComplexEmbedding.IsReal

/-!
# Fractional ideals of imaginary quadratic orders as period lattices

Let `K` be a quadratic number field with a complex embedding `σ : K →+* ℂ` that is not real, so `K`
is imaginary quadratic and `σ` is one of its two complex embeddings (the choice of `σ` is the
orientation). Let `O` be an order of `K` and `I` a nonzero fractional ideal of `O`. A `ℤ`-basis
`v₀, v₁` of `I` is a `ℚ`-basis of `K`, and `σ v₀, σ v₁` are linearly independent over `ℝ`: otherwise
every `σ x = p σ v₀ + q σ v₁` would lie on one real line through `0` together with `σ 1 = 1`,
making `σ` real. So `σ(I)` is the lattice of a period pair (`exists_periodPair_lattice_eq`), and
`I` has a complex elliptic curve `E_I = ℂ / σ(I)`. For the order of discriminant `-n` in the model
`ℚ(√-n)` with its distinguished embedding and an invertible ideal, this lattice is
`TauCeti.QuadraticOrder.complexFractionalIdeal`, studied through binary quadratic forms in
`TauCeti.NumberTheory.BinaryQuadraticForm.PicAction`; here the order, the field, the orientation
and the nonzero fractional ideal are arbitrary.

This file proves the endomorphism-order comparison for these lattices:

* the multiplier ring `{α ∈ ℂ | α σ(I) ⊆ σ(I)}` of the lattice, its left order
  `L.lattice.leftOrder`, is the image under `σ` of the multiplier ring `{x ∈ K | x I ⊆ I}` of the
  ideal (`toSubring_leftOrder_lattice_eq_map`);
* `O` lies in the multiplier ring of every fractional ideal, so it acts faithfully on `E_I(ℂ)` by
  the scalar maps (`orderEndRingHom_injective`);
* for a proper ideal the multiplier ring of the lattice is the image of `O` (`leftOrderEquiv`), so
  `O` gives exactly the scalar endomorphisms of `E_I(ℂ)` in the image of `PeriodPair.endRingHom`.

Homothetic ideals give homothetic lattices, hence isomorphic curves. So the `j`-invariant of
`E_I` depends only on the ideal class of `I` in the ideal class monoid of `O`
(`IdealClassMonoid.jInvariant`), and it is a value of the modular `j`-function
(`IdealClassMonoid.exists_jInvariant_eq_j`).

## Main definitions

* `TauCeti.GlobalNumberFields.NumberFieldOrder.leftOrderEquiv`: for a proper ideal `I`, the
  order is isomorphic to the multiplier ring of the lattice `σ(I)`, by `σ`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.orderEndRingHom`: the action of `O` on the points
  `E_I(ℂ)` by the scalar maps.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.jInvariant`: the `j`-invariant of the curve of a
  nonzero fractional ideal.
* `TauCeti.GlobalNumberFields.IdealClassMonoid.jInvariant`: its descent to ideal classes.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.exists_periodPair_lattice_eq`: `σ(I)` is the
  lattice of a period pair.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.toSubring_leftOrder_lattice_eq_map`: the
  multiplier ring of `σ(I)` is `σ` of the multiplier ring of `I`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.leftOrder_lattice_eq_map_of_isProper`: for a proper
  ideal it is `σ(O)`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.orderEndRingHom_injective`: `O` acts faithfully.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.jInvariant_eq_of_homothetyCon`: homothetic ideals
  have the same `j`-invariant.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Graduate Texts in
  Mathematics 151, Springer, 1994, §II.1.
* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §10.
-/

public noncomputable section

open NumberField FractionalIdeal

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K]

variable {O : NumberFieldOrder K} {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K}

/-- **The lattice of a fractional ideal.** If `K` is quadratic and `σ` is not real, the image of a
nonzero fractional ideal `I` of an order is the lattice of a period pair. -/
theorem exists_periodPair_lattice_eq (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) (hI : I ≠ 0) :
    ∃ L : PeriodPair, (L.lattice : Set ℂ) = σ '' I := by
  obtain ⟨b, hb⟩ := O.exists_basis_restrictScalars_eq_span hI
  set b' := b.reindex (finCongr hK)
  have hrange : Set.range b = {b' 0, b' 1} := by
    rw [← b.range_reindex (finCongr hK)]
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two]
    exact ⟨fun h ↦ h.imp Eq.symm Eq.symm, fun h ↦ h.imp Eq.symm Eq.symm⟩
  have hspan : Submodule.span ℚ {b' 0, b' 1} = ⊤ := by
    rw [← hrange]
    exact b.span_eq
  refine ⟨⟨σ (b' 0), σ (b' 1), NumberField.linearIndependent_real_of_span_rat_eq_top hσ hspan⟩, ?_⟩
  have hI' : (I : Set K) = Submodule.span ℤ {b' 0, b' 1} := by
    rw [← hrange, ← hb, Submodule.coe_restrictScalars, coeToSet_coeToSubmodule]
  rw [hI', PeriodPair.lattice]
  -- `σ` maps the `ℤ`-span of `b'` onto the `ℤ`-span of its image, as a `ℤ`-linear map.
  simpa [Set.image_pair] using
    congrArg SetLike.coe (Submodule.map_span σ.toIntAlgHom.toLinearMap {b' 0, b' 1}).symm

/-- **The endomorphism-order comparison.** If the lattice of `L` is `σ(I)`, its multiplier ring
`{α ∈ ℂ | α σ(I) ⊆ σ(I)}` is the image under `σ` of the multiplier ring of `I`. -/
theorem toSubring_leftOrder_lattice_eq_map {σ : K →+* ℂ} {L : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' I) :
    L.lattice.leftOrder.toSubring = (O.multiplierRing I).map σ := by
  have hmem : ∀ z, z ∈ L.lattice ↔ ∃ y ∈ I, σ y = z := fun z ↦ by
    rw [← SetLike.mem_coe, hL]
    rfl
  -- `σ(I)` contains the nonzero period `ω₁`.
  obtain ⟨y₀, hy₀, hσy₀⟩ := (hmem _).mp L.ω₁_mem_lattice
  replace hσy₀ : σ y₀ ≠ 0 := hσy₀ ▸ L.ω₁_ne_zero
  ext α
  rw [Subalgebra.mem_toSubring, Submodule.mem_leftOrder_iff, Subring.mem_map]
  constructor
  · intro h
    obtain ⟨y₁, -, e⟩ := (hmem _).mp (h _ ((hmem _).mpr ⟨y₀, hy₀, rfl⟩))
    have hα : σ (y₁ / y₀) = α := by rw [map_div₀, e, mul_div_cancel_right₀ _ hσy₀]
    refine ⟨y₁ / y₀, (O.mem_multiplierRing_iff I _).mpr fun y hy ↦ ?_, hα⟩
    obtain ⟨y', hy', e'⟩ := (hmem _).mp (h _ ((hmem _).mpr ⟨y, hy, rfl⟩))
    rwa [σ.injective (e'.trans (by rw [map_mul, hα]) : σ y' = σ (y₁ / y₀ * y))] at hy'
  · rintro ⟨x, hx, rfl⟩ z hz
    obtain ⟨y, hy, rfl⟩ := (hmem _).mp hz
    exact (hmem _).mpr ⟨x * y, (O.mem_multiplierRing_iff I x).mp hx y hy, map_mul σ x y⟩

/-- For a proper fractional ideal `I`, the multiplier ring of the lattice `σ(I)` is `σ(O)`. -/
theorem leftOrder_lattice_eq_map_of_isProper {σ : K →+* ℂ} (hI : O.IsProperFractionalIdeal I)
    {L : PeriodPair} (hL : (L.lattice : Set ℂ) = σ '' I) :
    L.lattice.leftOrder = O.toSubalgebra.map σ.toIntAlgHom := by
  refine Subalgebra.toSubring_injective ?_
  rw [toSubring_leftOrder_lattice_eq_map hL, (O.isProperFractionalIdeal_def I).mp hI]
  rfl

/-- For a proper fractional ideal `I`, the order is isomorphic by `σ` to the multiplier ring of the
lattice `σ(I)`. -/
def leftOrderEquiv {σ : K →+* ℂ} (hI : O.IsProperFractionalIdeal I) {L : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' I) : O.toSubalgebra ≃ₐ[ℤ] L.lattice.leftOrder :=
  (O.toSubalgebra.equivMapOfInjective σ.toIntAlgHom σ.injective).trans
    (Subalgebra.equivOfEq _ _ (leftOrder_lattice_eq_map_of_isProper hI hL).symm)

/-- `leftOrderEquiv` is `σ`. -/
@[simp]
lemma coe_leftOrderEquiv {σ : K →+* ℂ} (hI : O.IsProperFractionalIdeal I) {L : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' I) (x : O.toSubalgebra) :
    (leftOrderEquiv hI hL x : ℂ) = σ x :=
  (rfl)

/-- The action of the order on the points `E_I(ℂ)` of the curve of a fractional ideal `I`: `x ∈ O`
acts by the scalar map of `σ x`, which lies in the multiplier ring of `σ(I)` because `x I ⊆ I`. -/
def orderEndRingHom {σ : K →+* ℂ} {L : PeriodPair} (hL : (L.lattice : Set ℂ) = σ '' I) :
    O.toSubalgebra →+* AddMonoid.End L.weierstrassCurve.toAffine.Point :=
  L.endRingHom.comp ((σ.toIntAlgHom.comp O.toSubalgebra.val).codRestrict L.lattice.leftOrder
    fun x ↦ by
      have h : σ x ∈ L.lattice.leftOrder.toSubring := by
        rw [toSubring_leftOrder_lattice_eq_map hL]
        exact Subring.mem_map.mpr ⟨x, O.order_le_multiplierRing I x.property, rfl⟩
      exact h : O.toSubalgebra →+* L.lattice.leftOrder)

/-- An element `x` of the order acts on the curve of `I` by `P(z) ↦ P(σ(x) z)`. -/
@[simp]
lemma orderEndRingHom_weierstrassPoint {σ : K →+* ℂ} {L : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' I) (x : O.toSubalgebra) (z : ℂ) :
    orderEndRingHom hL x (L.weierstrassPoint z) = L.weierstrassPoint (σ x * z) :=
  L.endRingHom_weierstrassPoint _ z

/-- **The order acts faithfully** on the points of the curve of a fractional ideal. For a proper
ideal, `leftOrderEquiv` shows that every scalar endomorphism in the image of
`PeriodPair.endRingHom` comes from it. -/
theorem orderEndRingHom_injective {σ : K →+* ℂ} {L : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' I) :
    Function.Injective (orderEndRingHom hL) := fun _ _ h ↦
  Subtype.val_injective (σ.injective (congrArg Subtype.val (L.endRingHom_injective h)))

/-! ### The `j`-invariant of an ideal class -/

/-- If the lattice of `L` is `σ(I)` and `J = x I`, then the lattice of `σ(x) • L` is `σ(J)`. -/
lemma lattice_smul_eq_image_spanSingleton_mul {σ : K →+* ℂ} {L : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' I) (x : Kˣ) :
    (((Units.map σ.toMonoidHom x) • L).lattice : Set ℂ) =
      σ '' (spanSingleton (nonZeroDivisors O.toSubalgebra) (x : K) * I : FractionalIdeal _ K) := by
  have hmem : ∀ z, z ∈ L.lattice ↔ ∃ y ∈ I, σ y = z := fun z ↦ by
    rw [← SetLike.mem_coe, hL]
    rfl
  ext z
  simp only [SetLike.mem_coe, PeriodPair.lattice_smul, Submodule.mem_map, LinearMap.mulLeft_apply,
    Set.mem_image, mem_singleton_mul, hmem]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x * y, ⟨y, hy, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨σ y, ⟨y, hy, rfl⟩, by simp⟩

variable (O) in
/-- The `j`-invariant of the curve `ℂ / σ(I)` of a nonzero fractional ideal `I`. -/
def jInvariant (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ} (hσ : ¬ ComplexEmbedding.IsReal σ)
    (I : O.nonzeroFractionalIdeals) : ℂ :=
  (exists_periodPair_lattice_eq hK hσ
    (nonZeroDivisors.ne_zero I.property)).choose.weierstrassCurve.j

/-- The `j`-invariant of `I` is that of any period pair with lattice `σ(I)`. -/
lemma jInvariant_eq (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) (I : O.nonzeroFractionalIdeals) {L : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)) :
    O.jInvariant hK hσ I = L.weierstrassCurve.j := by
  have h := exists_periodPair_lattice_eq hK hσ (nonZeroDivisors.ne_zero I.property)
  simp only [jInvariant, PeriodPair.weierstrassCurve_eq_of_lattice_eq
    (SetLike.coe_injective (h.choose_spec.trans hL.symm))]

/-- Homothetic fractional ideals have the same `j`-invariant. -/
theorem jInvariant_eq_of_homothetyCon (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) {I J : O.nonzeroFractionalIdeals}
    (h : O.homothetyCon I J) : O.jInvariant hK hσ I = O.jInvariant hK hσ J := by
  obtain ⟨x, hx⟩ := (O.homothetyCon_iff).mp h
  obtain ⟨L, hL⟩ := exists_periodPair_lattice_eq hK hσ (nonZeroDivisors.ne_zero I.property)
  have hL' := lattice_smul_eq_image_spanSingleton_mul hL x
  rw [hx] at hL'
  rw [jInvariant_eq hK hσ I hL, jInvariant_eq hK hσ J hL',
    PeriodPair.weierstrassCurve_j_eq_of_lattice_eq_smul rfl]

end NumberFieldOrder

namespace IdealClassMonoid

variable {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K}

/-- The `j`-invariant of an ideal class of an order of an imaginary quadratic field, for the
orientation given by a non-real embedding `σ`: the `j`-invariant of the curve `ℂ / σ(I)` of any
representative `I` (`IdealClassMonoid.jInvariant_mk`), which
`NumberFieldOrder.jInvariant_eq_of_homothetyCon` shows is unchanged by homothety. -/
def jInvariant (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ} (hσ : ¬ ComplexEmbedding.IsReal σ)
    (c : IdealClassMonoid O) : ℂ :=
  O.jInvariant hK hσ (Function.surjInv (mk_surjective O) c)

/-- The `j`-invariant of the class of `I` is the `j`-invariant of `I`. -/
@[simp]
theorem jInvariant_mk (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) (I : O.nonzeroFractionalIdeals) :
    (mk O I).jInvariant hK hσ = O.jInvariant hK hσ I :=
  NumberFieldOrder.jInvariant_eq_of_homothetyCon hK hσ
    ((O.homothetyCon_iff).mpr ((mk_eq_mk_iff O).mp (Function.surjInv_eq (mk_surjective O) _)))

/-- The `j`-invariant of an ideal class is a value of the modular `j`-function: it is `j(τ)` for a
point `τ` of the upper half-plane with `σ(I)` homothetic to `ℤ τ + ℤ`. -/
theorem exists_jInvariant_eq_j (hK : Module.finrank ℚ K = 2) {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) (c : IdealClassMonoid O) :
    ∃ τ : UpperHalfPlane, c.jInvariant hK hσ = TauCeti.ModularForm.j τ := by
  obtain ⟨I, rfl⟩ := mk_surjective O c
  obtain ⟨L, hL⟩ := NumberFieldOrder.exists_periodPair_lattice_eq hK hσ
    (nonZeroDivisors.ne_zero I.property)
  obtain ⟨u, τ, hτ⟩ := L.exists_lattice_eq_smul_periodPair
  refine ⟨τ, ?_⟩
  rw [jInvariant_mk, NumberFieldOrder.jInvariant_eq hK hσ I hL,
    PeriodPair.weierstrassCurve_j_eq_of_lattice_eq_smul hτ,
    UpperHalfPlane.weierstrassCurve_j_periodPair]

end IdealClassMonoid

end TauCeti.GlobalNumberFields
