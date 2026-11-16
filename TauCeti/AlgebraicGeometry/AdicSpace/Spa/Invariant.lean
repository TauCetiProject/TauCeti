/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.RingTheory.Huber.Invariant
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Generalizing
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Invariant
import TauCeti.RingTheory.Huber.OpenIdeal
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent
import TauCeti.RingTheory.Valuation.Integral.Basic
import TauCeti.Topology.Algebra.TopologicallyNilpotent.Basic

/-!
# The adic spectrum of an invariant Huber pair

Let `G` be a finite group acting by continuous ring automorphisms on a Tate ring `A`, with no
assumption on `|G|`, completeness, Hausdorffness, or sheafiness. This file establishes Hansen's
orbit-space theorem for adic spectra:

* A valuation `w ∈ Spv A` is continuous if and only if its restriction to the fixed subring
  `Aᴳ = FixedPoints.subring A G` is continuous
  (`TauCeti.ValuationSpectrum.isContinuous_comap_subtype_fixedPoints_iff`). Combined with
  surjectivity and orbit fibres on `Spv A → Spv Aᴳ`, restriction `Cont(A) → Cont(Aᴳ)` is
  surjective with fibres the `G`-orbits
  (`TauCeti.ValuationSpectrum.exists_mem_cont_comap_subtype_fixedPoints_eq`).
* For any `G`-stable integrally closed subring `A⁺ ⊆ A`, `Spa(A, A⁺)` is the full preimage of
  `Spa(Aᴳ, A⁺ ∩ Aᴳ)` in `Spv A`
  (`TauCeti.ValuationSpectrum.mem_spa_iff_comap_subtype_fixedPoints_mem_spa`).
* For a Tate–Huber pair `P = (A, A⁺)` with `G`-stable plus ring `A⁺`, the map
  `Spa(A, A⁺) → Spa(Aᴳ, A⁺ ∩ Aᴳ)` induced by `P.invariantInclusion G` is surjective
  (`TauCeti.Huber.Pair.surjective_spaComap_invariantInclusion`), a quotient map
  (`TauCeti.Huber.Pair.isQuotientMap_spaComap_invariantInclusion`), and an open map
  (`TauCeti.Huber.Pair.isOpenMap_spaComap_invariantInclusion`), whose fibres are the `G`-orbits
  (`TauCeti.Huber.Pair.spaComap_invariantInclusion_eq_iff`), inducing a homeomorphism
  `|Spa(A, A⁺)| / G ≃ₜ |Spa(Aᴳ, A⁺ ∩ Aᴳ)|`
  (`TauCeti.Huber.Pair.spaOrbitHomeomorph`).
* The preimage of a rational subset `R(T/s)` of `Spa(Aᴳ, A⁺ ∩ Aᴳ)` is the `G`-stable rational
  subset `R(T/s)` of `Spa(A, A⁺)`
  (`TauCeti.Huber.Pair.spaComap_invariantInclusion_preimage_rationalSubset`,
  `TauCeti.ValuationSpectrum.comap_smul_mem_rationalSubset_image_fixedPoints_iff`), and any subset
  generating an open ideal of `Aᴳ` generates the unit ideal of `A`
  (`TauCeti.Huber.ideal_span_image_fixedPoints_eq_top`).

## Main definitions

* `TauCeti.ValuationSpectrum.spaOrbitSetoid`: the `G`-orbit equivalence relation on `Spa(A, A⁺)`
  for `v ↦ comap (g • ·) v`.
* `TauCeti.Huber.Pair.spaOrbitHomeomorph`: the homeomorphism
  `Quotient (spaOrbitSetoid G P.plus) ≃ₜ spa (P.invariant G).plus`.

## Main results

* `TauCeti.ValuationSpectrum.isContinuous_of_isContinuous_comap_of_isOpen_integer`: general
  continuity lifting along an integral extension with an open integer ring and a topologically
  nilpotent element mapping to a topologically nilpotent unit.
* `TauCeti.ValuationSpectrum.isContinuous_comap_subtype_fixedPoints_iff`: `w ∈ Spv A` is
  continuous iff its restriction to `Aᴳ` is continuous.
* `TauCeti.ValuationSpectrum.exists_mem_cont_comap_subtype_fixedPoints_eq`: `Cont(A) → Cont(Aᴳ)` is
  surjective.
* `TauCeti.ValuationSpectrum.mem_spa_iff_comap_subtype_fixedPoints_mem_spa`: `Spa(A, A⁺)` is the
  full preimage of `Spa(Aᴳ, A⁺ ∩ Aᴳ)` in `Spv A`.
* `TauCeti.Huber.Pair.isQuotientMap_spaComap_invariantInclusion`,
  `TauCeti.Huber.Pair.isOpenMap_spaComap_invariantInclusion`,
  `TauCeti.Huber.Pair.spaComap_invariantInclusion_eq_iff`: Hansen Theorem 3.1.

## References

* D. Hansen, *Quotients of adic spaces by finite groups*, Math. Res. Lett. 28 (2021), Theorem 3.1.
-/

public section

open Filter Topology TauCeti.Huber

namespace TauCeti

namespace ValuationSpectrum

private theorem comap_smul_inv_comap_smul {G A : Type*} [Group G] [CommRing A]
    [MulSemiringAction G A] (g : G) (v : Spv A) :
    comap (MulSemiringAction.toRingHom G A g⁻¹)
      (comap (MulSemiringAction.toRingHom G A g) v) = v := by
  have hcomp : (MulSemiringAction.toRingHom G A g).comp
      (MulSemiringAction.toRingHom G A g⁻¹) = RingHom.id A :=
    RingHom.ext fun a ↦ smul_inv_smul g a
  rw [comap_comap, hcomp, comap_id, _root_.id]

section ContinuityLifting

/-- **Continuity lifting along an integral extension.** Let `A → B` be an integral homomorphism into
a topological ring `B`, let `ϖ ∈ A` be topologically nilpotent with `algebraMap A B ϖ` a
topologically nilpotent unit of `B`, and let `w ∈ Spv B` have continuous restriction to `A` and
open integer ring `w.valuation.integer`. Then `w` is continuous.

This isolates the general continuity criterion underlying both the finite-algebra case
(`TauCeti.ValuationSpectrum.isContinuous_of_isContinuous_comap`) and the invariant-subring case
(`TauCeti.ValuationSpectrum.isContinuous_comap_subtype_fixedPoints_iff`). -/
theorem isContinuous_of_isContinuous_comap_of_isOpen_integer
    {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [Algebra A B] [Algebra.IsIntegral A B]
    {ϖ : A} (hϖ : IsTopologicallyNilpotent ϖ)
    (huϖ : IsUnit (algebraMap A B ϖ)) (hnϖ : IsTopologicallyNilpotent (algebraMap A B ϖ))
    {w : Spv B} (hw : (comap (algebraMap A B) w).IsContinuous)
    (hopen : IsOpen (w.valuation.integer : Set B)) : w.IsContinuous := by
  set V := w.valuation
  set ι := algebraMap A B
  have hϖ0 : V (ι ϖ) ≠ 0 := (huϖ.map V).ne_zero
  have hu : (V.comap ι).IsContinuous := by
    rw [isContinuous_def] at hw
    refine (Valuation.IsEquiv.isContinuous_iff fun x y ↦ ?_).mp hw
    rw [valuation_le_iff, comap_vle, ← valuation_le_iff, Valuation.comap_apply,
      Valuation.comap_apply]
  have habs (b : B) : ∃ m : ℕ, V (ι ϖ) ^ m * V b ≤ 1 := by
    obtain ⟨m, hm⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent hnϖ hopen b
    exact ⟨m, by simpa [mul_comm, Valuation.mem_integer_iff] using hm⟩
  rw [isContinuous_def, Valuation.isContinuous_iff_forall_ne_zero]
  intro c hc
  obtain ⟨N, hN⟩ := Valuation.exists_pow_lt_of_isIntegral hu hϖ hϖ0 habs hc
  obtain ⟨u, hιu⟩ := huϖ
  refine isOpen_iff_mem_nhds.mpr fun b₀ hb₀ ↦ ?_
  have hmem : {x : B | ((u⁻¹ : Bˣ) : B) ^ N * (x - b₀) ∈ V.integer} ∈ 𝓝 b₀ :=
    (hopen.preimage (by fun_prop)).mem_nhds (by simp [V.integer.zero_mem])
  filter_upwards [hmem] with x hx
  have hx' : V (x - b₀) ≤ V (ι ϖ) ^ N := by
    calc V (x - b₀) = V (ι ϖ) ^ N * V (((u⁻¹ : Bˣ) : B) ^ N * (x - b₀)) := by
          rw [← map_pow, ← map_mul, ← mul_assoc, ← hιu, ← mul_pow, Units.mul_inv, one_pow,
            one_mul]
      _ ≤ V (ι ϖ) ^ N * 1 := by gcongr; exact hx
      _ = V (ι ϖ) ^ N := mul_one _
  rw [← add_sub_cancel b₀ x]
  exact V.map_add_lt hb₀ (hx'.trans_lt hN)

end ContinuityLifting

section Action

variable {G A : Type*} [Group G] [CommRing A] [TopologicalSpace A] [MulSemiringAction G A]

/-- The `G`-orbit equivalence relation on `Spa(A, A⁺)` for the action `v ↦ comap (g • ·) v`. -/
def spaOrbitSetoid (G : Type*) {A : Type*} [Group G] [CommRing A] [TopologicalSpace A]
    [MulSemiringAction G A] (Aplus : Subring A) : Setoid (spa Aplus) where
  r v w := ∃ g : G, (w : Spv A) = comap (MulSemiringAction.toRingHom G A g) v
  iseqv :=
    { refl v := ⟨1, by
        have h1 : MulSemiringAction.toRingHom G A 1 = RingHom.id A :=
          RingHom.ext (one_smul G)
        rw [h1, comap_id, _root_.id]⟩
      symm := fun ⟨g, hg⟩ ↦ ⟨g⁻¹, by rw [hg, comap_smul_inv_comap_smul]⟩
      trans := fun ⟨g₁, h₁⟩ ⟨g₂, h₂⟩ ↦ ⟨g₁ * g₂, by
        rw [h₂, h₁, comap_comap]
        exact congrFun (congrArg comap (RingHom.ext fun a ↦ (mul_smul g₁ g₂ a).symm)) _⟩ }

/-- Two points of `Spa(A, A⁺)` are related by `spaOrbitSetoid G Aplus` iff one is obtained from
the other by pulling back along the action of some `g : G`. -/
@[simp]
theorem spaOrbitSetoid_iff (G : Type*) {A : Type*} [Group G] [CommRing A] [TopologicalSpace A]
    [MulSemiringAction G A] (Aplus : Subring A) {v w : spa Aplus} :
    spaOrbitSetoid G Aplus v w ↔
      ∃ g : G, (w : Spv A) = comap (MulSemiringAction.toRingHom G A g) v :=
  Iff.rfl

/-- Pullback along a continuous group automorphism preserves and reflects membership in `Cont A`. -/
theorem comap_smul_mem_cont_iff [ContinuousConstSMul G A] (g : G) {w : Spv A} :
    comap (MulSemiringAction.toRingHom G A g) w ∈ cont A ↔ w ∈ cont A := by
  simp only [mem_cont_iff]
  exact ⟨fun h ↦ by
      rw [← comap_smul_inv_comap_smul g w]
      exact h.comap (continuous_const_smul g⁻¹),
    fun h ↦ h.comap (continuous_const_smul g)⟩

/-- Pullback along a continuous group automorphism preserving `A⁺` preserves and reflects membership
in `Spa(A, A⁺)`. -/
theorem comap_smul_mem_spa_iff [ContinuousConstSMul G A] {Aplus : Subring A}
    (hAplus : ∀ g : G, ∀ a ∈ Aplus, g • a ∈ Aplus) (g : G) {w : Spv A} :
    comap (MulSemiringAction.toRingHom G A g) w ∈ spa Aplus ↔ w ∈ spa Aplus :=
  ⟨fun h ↦ by
      rw [← comap_smul_inv_comap_smul g w]
      exact comap_mem_spa (continuous_const_smul g⁻¹) (hAplus g⁻¹) h,
    comap_mem_spa (continuous_const_smul g) (hAplus g)⟩

open scoped Classical in
/-- **Rational subsets defined by `G`-invariant elements are `G`-stable.** If `G` acts continuously
on `A` preserving `A⁺`, then any rational subset `R(T/s)` whose parameters come from `Aᴳ` is
preserved under pullback by every `g : G`. -/
theorem comap_smul_mem_rationalSubset_image_fixedPoints_iff [ContinuousConstSMul G A]
    {Aplus : Subring A} (hAplus : ∀ g : G, ∀ a ∈ Aplus, g • a ∈ Aplus)
    (T : Finset (FixedPoints.subring A G)) (s : FixedPoints.subring A G) (g : G) {v : Spv A} :
    comap (MulSemiringAction.toRingHom G A g) v ∈
        rationalSubset Aplus (T.image (FixedPoints.subring A G).subtype) (s : A) ↔
      v ∈ rationalSubset Aplus (T.image (FixedPoints.subring A G).subtype) (s : A) := by
  simp only [mem_rationalSubset_iff, comap_smul_mem_spa_iff hAplus g, Finset.mem_image,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, comap_vle,
    MulSemiringAction.toRingHom_apply, Subring.coe_subtype, s.2 g, map_zero]
  refine and_congr_right fun _ ↦ and_congr_left fun _ ↦ forall₂_congr fun t _ ↦ ?_
  rw [t.2 g]

end Action

section FixedPoints

variable (G : Type*) {A : Type*} [Group G] [Finite G] [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsTateRing A] [MulSemiringAction G A] [ContinuousConstSMul G A]

/-- **Continuity descends along `Aᴳ → A`.** For a continuous action of a finite group `G` on a Tate
ring `A`, a point `w ∈ Spv A` is continuous if and only if its restriction to `Aᴳ` is continuous. -/
theorem isContinuous_comap_subtype_fixedPoints_iff {w : Spv A} :
    (comap (FixedPoints.subring A G).subtype w).IsContinuous ↔ w.IsContinuous := by
  refine ⟨fun hw ↦ ?_, fun hw ↦ hw.comap continuous_subtype_val⟩
  cases nonempty_fintype G
  have := Algebra.IsInvariant.isIntegral (FixedPoints.subring A G) A G
  obtain ⟨ϖ₀, hϖ₀⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  set ι := (FixedPoints.subring A G).subtype
  have hu : (w.valuation.comap ι).IsContinuous := by
    rw [isContinuous_def] at hw
    refine (Valuation.IsEquiv.isContinuous_iff fun x y ↦ ?_).mp hw
    rw [valuation_le_iff, comap_vle, ← valuation_le_iff, Valuation.comap_apply,
      Valuation.comap_apply]
  have hR : IsOpen ((w.valuation.comap ι).integer : Set (FixedPoints.subring A G)) := by
    simpa [Valuation.integer] using hu.isOpen_le (b := 1) (by simp)
  have hle : (integralClosure ((w.valuation.comap ι).integer.map ι) A).toSubring ≤
      w.valuation.integer :=
    Subring.integralClosure_subring_le_iff.mpr fun _ ⟨_, hx, hxe⟩ ↦ hxe ▸ hx
  have hopen : IsOpen (w.valuation.integer : Set A) :=
    AddSubgroup.isOpen_of_mem_nhds w.valuation.integer.toAddSubgroup <|
      Filter.mem_of_superset
        ((isOpen_integralClosure_map_subtype_fixedPoints hR).mem_nhds (Subring.zero_mem _)) hle
  exact isContinuous_of_isContinuous_comap_of_isOpen_integer
    (isTopologicallyNilpotent_orbitProd G hϖ₀.isTopologicallyNilpotent)
    (isPseudoUniformizer_coe_orbitProd G hϖ₀).isUnit
    (isPseudoUniformizer_coe_orbitProd G hϖ₀).isTopologicallyNilpotent hw hopen

/-- `Cont(A)` is the full preimage of `Cont(Aᴳ)` in `Spv A`. -/
theorem mem_cont_comap_subtype_fixedPoints_iff {w : Spv A} :
    comap (FixedPoints.subring A G).subtype w ∈ cont (FixedPoints.subring A G) ↔ w ∈ cont A := by
  rw [mem_cont_iff, mem_cont_iff]
  exact isContinuous_comap_subtype_fixedPoints_iff G

/-- **Surjectivity on continuous valuations.** Every continuous valuation on `Aᴳ` extends to a
continuous valuation on `A`. Together with `comap_subtype_fixedPoints_eq_iff`, the fibres of
`Cont(A) → Cont(Aᴳ)` are the `G`-orbits. -/
theorem exists_mem_cont_comap_subtype_fixedPoints_eq {v : Spv (FixedPoints.subring A G)}
    (hv : v ∈ cont (FixedPoints.subring A G)) :
    ∃ w ∈ cont A, comap (FixedPoints.subring A G).subtype w = v := by
  obtain ⟨w, rfl⟩ := comap_subtype_fixedPoints_surjective G v
  exact ⟨w, (mem_cont_comap_subtype_fixedPoints_iff G).mp hv, rfl⟩

/-- **`Spa(A, A⁺)` is the full preimage of `Spa(Aᴳ, A⁺ ∩ Aᴳ)` in `Spv A`.** For a `G`-stable
integrally closed subring `A⁺` of a Tate ring `A`, a valuation `w ∈ Spv A` lies in `Spa(A, A⁺)`
if and only if its restriction to `Aᴳ` lies in `Spa(Aᴳ, A⁺ ∩ Aᴳ)`. -/
theorem mem_spa_iff_comap_subtype_fixedPoints_mem_spa {Aplus : Subring A}
    [IsIntegrallyClosedIn Aplus A] (hAplus : ∀ g : G, ∀ a ∈ Aplus, g • a ∈ Aplus) {w : Spv A} :
    w ∈ spa Aplus ↔
      comap (FixedPoints.subring A G).subtype w ∈
        spa (Aplus.comap (FixedPoints.subring A G).subtype) := by
  have hcl : Aplus =
      (integralClosure ((Aplus.comap (FixedPoints.subring A G).subtype).map
        (FixedPoints.subring A G).subtype) A).toSubring := by
    rw [Subring.map_comap_eq, Subring.range_subtype]
    exact (Subring.integralClosure_inf_fixedPoints_eq G hAplus).symm
  refine ⟨comap_mem_spa continuous_subtype_val fun _ ha ↦ ha, fun hw ↦ ?_⟩
  rw [hcl, spa_integralClosure]
  exact (mem_spa_map_iff continuous_subtype_val _
    ((isContinuous_comap_subtype_fixedPoints_iff G).mp ((mem_spa_iff _ _).mp hw).1)).mpr hw

end FixedPoints

end ValuationSpectrum

namespace Huber

/-- A subset of `Aᴳ` that generates an open ideal of `Aᴳ` generates the unit ideal of `A`, since
`Aᴳ` is a Tate ring (`TauCeti.Huber.isTateRing_fixedPoints`). -/
theorem ideal_span_image_fixedPoints_eq_top (G : Type*) {A : Type*} [Group G] [Finite G]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
    [MulSemiringAction G A] [ContinuousConstSMul G A] {T : Set (FixedPoints.subring A G)}
    (hT : IsOpen (Ideal.span T : Set (FixedPoints.subring A G))) :
    Ideal.span ((FixedPoints.subring A G).subtype '' T) = ⊤ := by
  rw [← Ideal.map_span, IsTateRing.eq_top_of_isOpen hT, Ideal.map_top]

namespace Pair

open ValuationSpectrum

variable (G : Type*) {A : Type*} [Group G] [Finite G] [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsTateRing A] [MulSemiringAction G A] [ContinuousConstSMul G A]

/-- **Fibres of `Spa(A, A⁺) → Spa(Aᴳ, A⁺ ∩ Aᴳ)` are the `G`-orbits.** Two points of `Spa(A, A⁺)`
have the same restriction to `Aᴳ` if and only if they lie in the same `G`-orbit. -/
theorem spaComap_invariantInclusion_eq_iff (P : Pair A) {v w : spa P.plus} :
    (P.invariantInclusion G).spaComap v = (P.invariantInclusion G).spaComap w ↔
      ∃ g : G, (w : Spv A) = comap (MulSemiringAction.toRingHom G A g) v := by
  rw [Subtype.ext_iff, Hom.spaComap_val, Hom.spaComap_val, toRingHom_invariantInclusion,
    comap_subtype_fixedPoints_eq_iff]

/-- **Surjectivity of `Spa(A, A⁺) → Spa(Aᴳ, A⁺ ∩ Aᴳ)`.** When `G` preserves `A⁺`, every point of
`Spa(Aᴳ, A⁺ ∩ Aᴳ)` lifts to `Spa(A, A⁺)`. -/
theorem surjective_spaComap_invariantInclusion (P : Pair A)
    (hP : ∀ g : G, ∀ a ∈ P.plus, g • a ∈ P.plus) :
    Function.Surjective (P.invariantInclusion G).spaComap := by
  have := P.isRingOfIntegralElements.isIntegrallyClosedIn
  intro x
  obtain ⟨w, hw⟩ := comap_subtype_fixedPoints_surjective G x.1
  have hx : x.1 ∈ spa (P.plus.comap (FixedPoints.subring A G).subtype) :=
    (invariant_plus G P) ▸ x.2
  refine ⟨⟨w, (mem_spa_iff_comap_subtype_fixedPoints_mem_spa G hP).mpr (hw ▸ hx)⟩, Subtype.ext ?_⟩
  rw [Hom.spaComap_val, toRingHom_invariantInclusion, hw]

/-- **Hansen Theorem 3.1 (quotient map).** For a continuous action of a finite group `G` on a
Tate–Huber pair `(A, A⁺)` preserving `A⁺`, the restriction map `Spa(A, A⁺) → Spa(Aᴳ, A⁺ ∩ Aᴳ)` is
a topological quotient map. -/
theorem isQuotientMap_spaComap_invariantInclusion (P : Pair A)
    (hP : ∀ g : G, ∀ a ∈ P.plus, g • a ∈ P.plus) :
    Topology.IsQuotientMap (P.invariantInclusion G).spaComap :=
  (P.invariantInclusion G).isQuotientMap_spaComap_of_isTateRing
    (surjective_spaComap_invariantInclusion G P hP)

/-- **Hansen Theorem 3.1 (openness).** For a continuous action of a finite group `G` on a
Tate–Huber pair `(A, A⁺)` preserving `A⁺`, the restriction map `Spa(A, A⁺) → Spa(Aᴳ, A⁺ ∩ Aᴳ)` is
an open map. -/
theorem isOpenMap_spaComap_invariantInclusion (P : Pair A)
    (hP : ∀ g : G, ∀ a ∈ P.plus, g • a ∈ P.plus) :
    IsOpenMap (P.invariantInclusion G).spaComap := by
  have hquot := isQuotientMap_spaComap_invariantInclusion G P hP
  let σ (g : G) : spa P.plus → spa P.plus :=
    fun y ↦ ⟨_, (comap_smul_mem_spa_iff hP g).mpr y.2⟩
  have hσ (g : G) : Continuous (σ g) :=
    ((continuous_comap _).comp continuous_subtype_val).subtype_mk _
  intro U hU
  rw [← hquot.isOpen_preimage]
  convert isOpen_iUnion fun g ↦ hU.preimage (hσ g) using 1
  ext y
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨u, hu, huy⟩
    obtain ⟨g, hg⟩ := (spaComap_invariantInclusion_eq_iff G P).mp huy
    refine ⟨g⁻¹, ?_⟩
    convert hu using 1
    exact Subtype.ext <| by simpa [σ, hg] using comap_smul_inv_comap_smul g u.1
  · rintro ⟨g, hg⟩
    exact ⟨σ g y, hg,
      (spaComap_invariantInclusion_eq_iff G P).mpr ⟨g⁻¹, (comap_smul_inv_comap_smul g y.1).symm⟩⟩

/-- **Hansen Theorem 3.1 (orbit-space homeomorphism).** For a continuous action of a finite group
`G` on a Tate–Huber pair `(A, A⁺)` preserving `A⁺`, restriction induces a homeomorphism
`|Spa(A, A⁺)| / G ≃ₜ |Spa(Aᴳ, A⁺ ∩ Aᴳ)|`. -/
noncomputable def spaOrbitHomeomorph (P : Pair A)
    (hP : ∀ g : G, ∀ a ∈ P.plus, g • a ∈ P.plus) :
    Quotient (spaOrbitSetoid G P.plus) ≃ₜ spa (P.invariant G).plus :=
  (Homeomorph.Quotient.congrRight (r' := Setoid.ker (P.invariantInclusion G).spaComap) fun _ _ ↦
    (spaOrbitSetoid_iff G P.plus).trans (spaComap_invariantInclusion_eq_iff G P).symm).trans
    (Topology.IsQuotientMap.homeomorph
      (f := ⟨(P.invariantInclusion G).spaComap, (P.invariantInclusion G).continuous_spaComap⟩)
      (isQuotientMap_spaComap_invariantInclusion G P hP))

/-- On orbit classes, `spaOrbitHomeomorph` evaluates as `(P.invariantInclusion G).spaComap`. -/
@[simp]
theorem spaOrbitHomeomorph_mk (P : Pair A)
    (hP : ∀ g : G, ∀ a ∈ P.plus, g • a ∈ P.plus) (v : spa P.plus) :
    spaOrbitHomeomorph G P hP (Quotient.mk _ v) = (P.invariantInclusion G).spaComap v := (rfl)

/-- The inverse of `spaOrbitHomeomorph` sends the restriction of `v` to the orbit class of `v`. -/
@[simp]
theorem spaOrbitHomeomorph_symm_spaComap (P : Pair A)
    (hP : ∀ g : G, ∀ a ∈ P.plus, g • a ∈ P.plus) (v : spa P.plus) :
    (spaOrbitHomeomorph G P hP).symm ((P.invariantInclusion G).spaComap v) = Quotient.mk _ v :=
  (spaOrbitHomeomorph G P hP).symm_apply_eq.mpr (spaOrbitHomeomorph_mk G P hP v).symm

open scoped Classical in
/-- **Preimages of rational subsets.** The preimage of a rational subset `R(T/s)` of
`Spa(Aᴳ, A⁺ ∩ Aᴳ)` under `Spa(A, A⁺) → Spa(Aᴳ, A⁺ ∩ Aᴳ)` is the rational subset `R(T/s)` of
`Spa(A, A⁺)`. -/
theorem spaComap_invariantInclusion_preimage_rationalSubset (P : Pair A)
    (T : Finset (FixedPoints.subring A G)) (s : FixedPoints.subring A G) :
    (P.invariantInclusion G).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset (P.invariant G).plus T s) =
      Subtype.val ⁻¹'
        rationalSubset P.plus (T.image (FixedPoints.subring A G).subtype) (s : A) := by
  simpa only [toRingHom_invariantInclusion, Subring.coe_subtype] using
    (P.invariantInclusion G).spaComap_preimage_rationalSubset T s

end Pair

end Huber

end TauCeti
