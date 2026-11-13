/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Pair
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Valuation

/-!
# The tilting map on adic spectra

Let `B` be a complete Hausdorff uniform Tate ring in which `p` is topologically nilpotent, and
assume its tilt `B♭ = uniformTilt p B` is a Tate ring (which holds whenever `B` is a perfectoid
Tate ring, or more generally receives a continuous homomorphism from a perfectoid Tate ring).
Given a Huber pair `P = (B, B⁺)` with tilted pair `P♭ = (B♭, B♭⁺)`, a point `x ∈ Spa(B, B⁺)`
represented by a continuous valuation `v_x` pulls back along the multiplicative sharp map
`♯ : B♭ → B` (`x ↦ x⁽⁰⁾`) to a continuous valuation `v_x ∘ ♯` (`uniformTilt.sharpValuation`) on
`B♭` taking values `≤ 1` on `B♭⁺`.

This defines the *tilting map* `spaTilt P : spa P.plus → spa (P.tilt (p := p)).plus`, which:

* is characterized by `(spaTilt P x)(f) ≤ (spaTilt P x)(g) ↔ x(f♯) ≤ x(g♯)`;
* gives the tilted point `x♭ = spaTilt P x` with support ideal `♯ ⁻¹' supp(x)`;
* pulls back rational subsets `R(T / s)` of `Spa(B♭, B♭⁺)` to `R(T♯ / s♯)` on `Spa(B, B⁺)` and
  preserves the rational family `spaRationalFamily` and `spaRationalOpens`;
* is continuous, and functorial in morphisms of Huber pairs;
* for a perfect ring `B` of characteristic `p`, agrees with `(Pair.tiltPairHomOfCharP P).spaComap`
  and has two-sided inverse `(Pair.tiltPairHomOfCharPSymm P).spaComap`.

## Main definitions

* `TauCeti.PerfectoidSpace.spaTilt`: the continuous tilting map `spa P.plus → spa (P.tilt).plus`.

## Main results

* `TauCeti.PerfectoidSpace.spaTilt_val`: underlying valuation-spectrum point via `sharpValuation`.
* `TauCeti.PerfectoidSpace.spaTilt_vle_iff`, `TauCeti.PerfectoidSpace.spaTilt_vlt_iff`:
  valuative comparisons at `spaTilt P x` are comparisons at `x` after applying `♯`.
* `TauCeti.PerfectoidSpace.mem_supp_spaTilt_iff`, `TauCeti.PerfectoidSpace.supp_spaTilt`:
  support of the tilted point.
* `TauCeti.PerfectoidSpace.spaTilt_eq_of_vle_iff`: uniqueness of `spaTilt P x` from its
  valuative relation on sharp images.
* `TauCeti.PerfectoidSpace.continuous_spaTilt`: continuity of `spaTilt P`.
* `TauCeti.PerfectoidSpace.spaTilt_preimage_rationalSubset`,
  `TauCeti.PerfectoidSpace.comap_spaTilt_spaBasicOpen`,
  `TauCeti.PerfectoidSpace.spaTilt_preimage_mem_spaRationalFamily`,
  `TauCeti.PerfectoidSpace.comap_spaTilt_mem_spaRationalOpens`: preimages of rational subsets and
  rational opens.
* `TauCeti.PerfectoidSpace.spaTilt_spaComap`, `TauCeti.PerfectoidSpace.spaTilt_comp_spaComap`:
  naturality for morphisms of Huber pairs.
* `TauCeti.PerfectoidSpace.spaTilt_eq_spaComap_tiltPairHomOfCharP`,
  `TauCeti.PerfectoidSpace.spaComap_tiltPairHomOfCharPSymm_spaTilt`,
  `TauCeti.PerfectoidSpace.spaComap_tiltPairHomOfCharPSymm_comp_spaTilt`,
  `TauCeti.PerfectoidSpace.spaTilt_spaComap_tiltPairHomOfCharPSymm`,
  `TauCeti.PerfectoidSpace.spaTilt_comp_spaComap_tiltPairHomOfCharPSymm`: for a perfect ring `B`
  of characteristic `p`, `spaTilt` agrees with `(Pair.tiltPairHomOfCharP P).spaComap` and is
  mutually inverse to `(Pair.tiltPairHomOfCharPSymm P).spaComap`.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §6, Theorem 6.3 and proof.
* P. Scholze, *Étale cohomology of diamonds*, §3, Theorem 3.12.
* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*, Arizona
  Winter School 2017, Lemma 2.6.12.
-/

public section

open Filter Topology TauCeti.Huber TauCeti.Perfectoid TauCeti.ValuationSpectrum

namespace TauCeti.PerfectoidSpace

section TiltMap

variable {p : ℕ} [hp : Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))] [IsTateRing (uniformTilt p B)]

/-- **The tilting map on adic spectra** `Spa(B, B⁺) → Spa(B♭, B♭⁺)`: sends a point `x` to the
point `x♭` whose underlying valuation is `v_x ∘ ♯` (Scholze, *Perfectoid spaces*, Theorem 6.3;
Kedlaya, *AWS 2017*, Lemma 2.6.12). -/
noncomputable def spaTilt (P : Pair B) (x : spa P.plus) : spa (P.tilt (p := p)).plus :=
  ⟨ofValuation (uniformTilt.sharpValuation x.1.valuation
      ((isContinuous_def x.1).mp ((mem_spa_iff P.plus x.1).mp x.2).1)),
    (mem_spa_iff _ _).mpr
      ⟨(isContinuous_ofValuation_iff _).mpr
          (uniformTilt.sharpValuation_isContinuous x.1.valuation
            ((isContinuous_def x.1).mp ((mem_spa_iff P.plus x.1).mp x.2).1)),
        fun a ha ↦ by
          rw [vle_ofValuation, uniformTilt.sharpValuation_apply, uniformTilt.sharpValuation_apply,
            valuation_le_iff, map_one]
          rw [Pair.tilt_plus] at ha
          exact ((mem_spa_iff P.plus x.1).mp x.2).2 _
            (uniformTilt.mem_plusSubring_iff_coeff_zero.mp ha)⟩⟩

/-- The underlying valuation-spectrum point of `spaTilt P x` is represented by
`uniformTilt.sharpValuation` applied to a representative valuation of `x`. -/
theorem spaTilt_val (P : Pair B) (x : spa P.plus) :
    (spaTilt (p := p) P x).1 =
      ofValuation (uniformTilt.sharpValuation x.1.valuation
        ((isContinuous_def x.1).mp ((mem_spa_iff P.plus x.1).mp x.2).1)) :=
  (rfl)

/-- **Characterisation of `spaTilt`**: `(spaTilt P x)(f) ≤ (spaTilt P x)(g)` iff `x(f♯) ≤ x(g♯)`. -/
@[simp]
theorem spaTilt_vle_iff (P : Pair B) (x : spa P.plus) (f g : uniformTilt p B) :
    (spaTilt (p := p) P x).1.toValuativeRel.vle f g ↔
      x.1.toValuativeRel.vle (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g) := by
  rw [spaTilt_val, vle_ofValuation, uniformTilt.sharpValuation_apply,
    uniformTilt.sharpValuation_apply]
  exact valuation_le_iff x.1 _ _

/-- **Strict comparison under `spaTilt`**: `(spaTilt P x)(f) < (spaTilt P x)(g)` iff
`x(f♯) < x(g♯)`. -/
@[simp]
theorem spaTilt_vlt_iff (P : Pair B) (x : spa P.plus) (f g : uniformTilt p B) :
    (spaTilt (p := p) P x).1.toValuativeRel.vlt f g ↔
      x.1.toValuativeRel.vlt (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g) :=
  not_congr (spaTilt_vle_iff P x g f)

/-- Membership in the support of `x♭`: `f ∈ supp(x♭) ↔ f♯ ∈ supp(x)`. -/
theorem mem_supp_spaTilt_iff (P : Pair B) (x : spa P.plus) (f : uniformTilt p B) :
    f ∈ (spaTilt (p := p) P x).1.supp ↔ uniformTilt.coeff p B 0 f ∈ x.1.supp := by
  simp only [mem_supp_iff, spaTilt_vle_iff, uniformTilt.coeff_zero]

/-- The support ideal of `x♭` is the preimage under `♯` of the support ideal of `x`. -/
theorem supp_spaTilt (P : Pair B) (x : spa P.plus) :
    ((spaTilt (p := p) P x).1.supp : Set (uniformTilt p B)) =
      (uniformTilt.coeff p B 0) ⁻¹' (x.1.supp : Set B) := by
  ext f
  simp

/-- Uniqueness of the tilted point: any point of `Spa(B♭, B♭⁺)` whose valuative relation agrees
with `x` on sharp images equals `spaTilt P x`. -/
theorem spaTilt_eq_of_vle_iff (P : Pair B) {x : spa P.plus} {y : spa (P.tilt (p := p)).plus}
    (h : ∀ f g, y.1.toValuativeRel.vle f g ↔
      x.1.toValuativeRel.vle (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g)) :
    spaTilt (p := p) P x = y :=
  Subtype.ext (ValuationSpectrum.ext' fun f g ↦ (spaTilt_vle_iff P x f g).trans (h f g).symm)

open scoped Classical in
/-- Preimage of a rational subset under `spaTilt` (Scholze, *Perfectoid spaces*, proof of
Theorem 6.3): `spaTilt⁻¹(R(T / s)) = R(T♯ / s♯)`. -/
theorem spaTilt_preimage_rationalSubset (P : Pair B) (T : Finset (uniformTilt p B))
    (s : uniformTilt p B) :
    spaTilt (p := p) P ⁻¹' (Subtype.val ⁻¹' rationalSubset (P.tilt (p := p)).plus T s) =
      Subtype.val ⁻¹'
        rationalSubset P.plus (T.image (uniformTilt.coeff p B 0)) (uniformTilt.coeff p B 0 s) := by
  ext x
  simp only [Set.mem_preimage, mem_rationalSubset_iff, Subtype.coe_prop, true_and,
    Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, spaTilt_vle_iff,
    uniformTilt.coeff_zero]

/-- **Continuity of the tilting map**: `spaTilt P : spa P.plus → spa (P.tilt).plus` is
continuous. -/
@[fun_prop, continuity]
theorem continuous_spaTilt (P : Pair B) : Continuous (spaTilt (p := p) P) := by
  classical
  refine (isTopologicalBasis_spaRationalFamily (P.tilt (p := p)).plus).continuous_iff.mpr ?_
  intro U hU
  obtain ⟨T, s, -, rfl⟩ := mem_spaRationalFamily_iff.mp hU
  rw [spaTilt_preimage_rationalSubset]
  exact isOpen_val_preimage_rationalSubset _ _ _

open scoped Classical in
/-- Preimage of a basic open `spaBasicOpen` under `spaTilt` as an equality in
`TopologicalSpace.Opens`. -/
@[simp]
theorem comap_spaTilt_spaBasicOpen (P : Pair B) (T : Finset (uniformTilt p B))
    (s : uniformTilt p B) :
    TopologicalSpace.Opens.comap ⟨spaTilt (p := p) P, continuous_spaTilt P⟩
        (spaBasicOpen (P.tilt (p := p)).plus T s) =
      spaBasicOpen P.plus (T.image (uniformTilt.coeff p B 0)) (uniformTilt.coeff p B 0 s) := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x ↦ ?_)
  simp only [SetLike.mem_coe, TopologicalSpace.Opens.mem_comap, ContinuousMap.coe_mk,
    mem_spaBasicOpen]
  exact Set.ext_iff.mp (spaTilt_preimage_rationalSubset P T s) x

/-- Rational subsets pull back along `spaTilt P` to rational subsets. -/
theorem spaTilt_preimage_mem_spaRationalFamily (P : Pair B)
    {U : Set (spa (P.tilt (p := p)).plus)}
    (hU : U ∈ spaRationalFamily (P.tilt (p := p)).plus) :
    spaTilt (p := p) P ⁻¹' U ∈ spaRationalFamily P.plus := by
  classical
  obtain ⟨T₀, s₀, hT₀, rfl⟩ := mem_spaRationalFamily_iff.mp hU
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := uniformTilt p B)
  obtain ⟨N, T, s, -, -, hEq⟩ :=
    ValuationSpectrum.exists_rationalSubset_eq_insert_pseudoUniformizer_pow
      (P.tilt (p := p)).plus (P.tilt (p := p)).isRingOfIntegralElements.isOpen hϖ T₀ s₀ hT₀
  rw [hEq, spaTilt_preimage_rationalSubset]
  exact mem_spaRationalFamily_iff.mpr
    ⟨_, _, uniformTilt.isOpen_span_image_coeff_zero_of_exists_isUnit _
      ⟨ϖ ^ N, Finset.mem_insert_self _ _, hϖ.isUnit.pow N⟩, rfl⟩

/-- Rational opens pull back along `spaTilt P` to rational opens. -/
theorem comap_spaTilt_mem_spaRationalOpens (P : Pair B)
    {U : TopologicalSpace.Opens (spa (P.tilt (p := p)).plus)}
    (hU : U ∈ spaRationalOpens (P.tilt (p := p)).plus) :
    TopologicalSpace.Opens.comap ⟨spaTilt (p := p) P, continuous_spaTilt P⟩ U ∈
      spaRationalOpens P.plus :=
  mem_spaRationalOpens.mpr (spaTilt_preimage_mem_spaRationalFamily P (mem_spaRationalOpens.mp hU))

end TiltMap

section Naturality

variable {p : ℕ} [Fact p.Prime] {B C : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))] [IsTateRing (uniformTilt p B)]
  [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsTateRing C]
  [CompleteSpace C] [T2Space C] [IsUniform C] [Fact (IsTopologicallyNilpotent (p : C))]
  [IsTateRing (uniformTilt p C)]

/-- **Naturality of `spaTilt`**, pointwise: for a morphism `φ : P → Q` of Huber pairs,
`spaTilt P (φ.spaComap x) = φ♭.spaComap (spaTilt Q x)`. -/
@[simp]
theorem spaTilt_spaComap {P : Pair B} {Q : Pair C} (φ : Pair.Hom P Q) (x : spa Q.plus) :
    spaTilt (p := p) P (φ.spaComap x) = (φ.tilt (p := p)).spaComap (spaTilt (p := p) Q x) := by
  refine spaTilt_eq_of_vle_iff (p := p) P fun f g ↦ ?_
  rw [Pair.Hom.spaComap_val, Pair.Hom.spaComap_val]
  simp

/-- **Naturality of `spaTilt`**: `spaTilt P ∘ φ.spaComap = φ♭.spaComap ∘ spaTilt Q`. -/
theorem spaTilt_comp_spaComap {P : Pair B} {Q : Pair C} (φ : Pair.Hom P Q) :
    spaTilt (p := p) P ∘ φ.spaComap = (φ.tilt (p := p)).spaComap ∘ spaTilt (p := p) Q :=
  funext (spaTilt_spaComap φ)

end Naturality

section CharP

variable {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))] [CharP B p] [PerfectRing B p]
  [IsTateRing (uniformTilt p B)]

/-- **For a perfect ring `B` of characteristic `p`, `spaTilt` is the pullback along
`uniformTilt.equivOfCharP`**: specifically `spaTilt P = (Pair.tiltPairHomOfCharP P).spaComap`. -/
theorem spaTilt_eq_spaComap_tiltPairHomOfCharP (P : Pair B) :
    spaTilt (p := p) P = (Pair.tiltPairHomOfCharP (p := p) P).spaComap := by
  funext x
  refine spaTilt_eq_of_vle_iff (p := p) P fun f g ↦ ?_
  rw [Pair.Hom.spaComap_val]
  simp

/-- For a perfect ring `B` of characteristic `p`, pullback along
`Pair.tiltPairHomOfCharPSymm` is left inverse to `spaTilt`, pointwise. -/
@[simp]
theorem spaComap_tiltPairHomOfCharPSymm_spaTilt (P : Pair B) (x : spa P.plus) :
    (Pair.tiltPairHomOfCharPSymm (p := p) P).spaComap (spaTilt (p := p) P x) = x := by
  apply Subtype.ext
  apply ValuationSpectrum.ext'
  intro f g
  rw [Pair.Hom.spaComap_val]
  simp

/-- For a perfect ring `B` of characteristic `p`, pullback along
`Pair.tiltPairHomOfCharPSymm` is left inverse to `spaTilt`. -/
@[simp]
theorem spaComap_tiltPairHomOfCharPSymm_comp_spaTilt (P : Pair B) :
    (Pair.tiltPairHomOfCharPSymm (p := p) P).spaComap ∘ spaTilt (p := p) P = id :=
  funext (spaComap_tiltPairHomOfCharPSymm_spaTilt P)

/-- For a perfect ring `B` of characteristic `p`, pullback along
`Pair.tiltPairHomOfCharPSymm` is right inverse to `spaTilt`, pointwise. -/
@[simp]
theorem spaTilt_spaComap_tiltPairHomOfCharPSymm (P : Pair B) (y : spa (P.tilt (p := p)).plus) :
    spaTilt (p := p) P ((Pair.tiltPairHomOfCharPSymm (p := p) P).spaComap y) = y := by
  refine spaTilt_eq_of_vle_iff (p := p) P fun f g ↦ ?_
  rw [Pair.Hom.spaComap_val]
  simp

/-- For a perfect ring `B` of characteristic `p`, pullback along
`Pair.tiltPairHomOfCharPSymm` is right inverse to `spaTilt`. -/
@[simp]
theorem spaTilt_comp_spaComap_tiltPairHomOfCharPSymm (P : Pair B) :
    spaTilt (p := p) P ∘ (Pair.tiltPairHomOfCharPSymm (p := p) P).spaComap = id :=
  funext (spaTilt_spaComap_tiltPairHomOfCharPSymm P)

end CharP

end TauCeti.PerfectoidSpace
