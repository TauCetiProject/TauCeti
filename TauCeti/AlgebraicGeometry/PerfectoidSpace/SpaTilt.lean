/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Perfectoid.UniformTilt.CharP
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Gauge
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Pair

/-!
# The tilting map on adic spectra

Let `B` be a complete Hausdorff uniform Tate ring in which `p` is topologically nilpotent, and
assume its tilt `B♭ = uniformTilt p B` is a Tate ring (which holds whenever `B` is a perfectoid
Tate ring, or more generally receives a continuous homomorphism from a perfectoid Tate ring).
Given a Huber pair `P = (B, B⁺)` with tilted pair `P♭ = (B♭, B♭⁺)`, a point `x ∈ Spa(B, B⁺)`
represented by a continuous valuation `v_x` pulls back along the multiplicative sharp map
`♯ : B♭ → B` (`x ↦ x⁽⁰⁾`) to a continuous valuation `v_x ∘ ♯` on `B♭` taking values `≤ 1` on
`B♭⁺`. Although `♯` is not additive, the limit formula `(a + b)♯ = lim_n (a⁽ⁿ⁾ + b⁽ⁿ⁾)^{pⁿ}`
together with continuity of `v_x` gives the ultrametric inequality
`v_x((a + b)♯) ≤ max (v_x(a♯)) (v_x(b♯))`.

This defines the *tilting map* `spaTilt P : spa P.plus → spa (P.tilt (p := p)).plus`, which:

* is characterized by `(spaTilt P x)(f) ≤ (spaTilt P x)(g) ↔ x(f♯) ≤ x(g♯)`;
* sends the support ideal of `x♭` to the preimage under `♯` of the support ideal of `x`;
* pulls back rational subsets `R(T / s)` of `Spa(B♭, B♭⁺)` to `R(T♯ / s♯)` on `Spa(B, B⁺)`,
  preserving openness of the numerator ideal whenever `T` contains a unit of `B♭`;
* is continuous, and functorial in morphisms of Huber pairs;
* identifies with the canonical homeomorphism induced by `uniformTilt.equivOfCharP` in
  characteristic `p`.

Moreover, every rational subset of `Spa(B♭, B♭⁺)` with open numerator ideal can be presented as
`R((insert (ϖ♭ ^ N) T) / s)` with `T ⊆ B♭⁺`, `s ∈ B♭⁺`, and `ϖ♭` a pseudouniformiser.

## Main definitions

* `TauCeti.PerfectoidSpace.spaTilt`: the continuous tilting map `spa P.plus → spa (P.tilt).plus`.

## Main results

* `TauCeti.PerfectoidSpace.spaTilt_vle_iff`, `TauCeti.PerfectoidSpace.spaTilt_vlt_iff`:
  valuative comparisons at `spaTilt P x` are comparisons at `x` after applying `♯`.
* `TauCeti.PerfectoidSpace.mem_supp_spaTilt_iff`, `TauCeti.PerfectoidSpace.supp_spaTilt`:
  support of the tilted point.
* `TauCeti.PerfectoidSpace.spaTilt_eq_of_vle_iff`: uniqueness of `spaTilt P x` from its
  valuative relation on sharp images.
* `TauCeti.PerfectoidSpace.spaTilt_preimage_rationalSubset`,
  `TauCeti.PerfectoidSpace.spaTilt_preimage_spaBasicOpen`: preimages of rational subsets.
* `TauCeti.PerfectoidSpace.isOpen_span_image_coeff_zero_of_exists_isUnit`: unit-containing
  numerator sets tilt to open numerator ideals.
* `TauCeti.PerfectoidSpace.continuous_spaTilt`: continuity of `spaTilt P`.
* `TauCeti.PerfectoidSpace.exists_rationalSubset_eq_insert_pseudoUniformizer_pow_tilt`,
  `TauCeti.PerfectoidSpace.exists_rationalSubset_eq_insert_pseudoUniformizerRoots_pow_tilt`:
  normalisation of rational subsets of `Spa(B♭, B♭⁺)` using a pseudouniformiser power.
* `TauCeti.PerfectoidSpace.spaTilt_spaComap`, `TauCeti.PerfectoidSpace.spaTilt_comp_spaComap`:
  naturality for morphisms of Huber pairs.
* `TauCeti.PerfectoidSpace.spaTilt_eq_spaComap_of_charP`,
  `TauCeti.PerfectoidSpace.spaComap_symm_spaTilt_of_charP`,
  `TauCeti.PerfectoidSpace.spaTilt_spaComap_symm_of_charP`: in characteristic `p`, `spaTilt`
  is the homeomorphism induced by `uniformTilt.equivOfCharP`.

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
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]

/-- Pulling back a continuous valuation `v` on `B` along the sharp map `♯ : uniformTilt p B → B`
yields a valuation on `uniformTilt p B`. -/
private noncomputable def sharpValuation {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation B Γ₀) (hv : v.IsContinuous) : Valuation (uniformTilt p B) Γ₀ where
  toFun a := v (uniformTilt.coeff p B 0 a)
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := by simp
  map_add_le_max' a b := by
    by_contra! hlt
    have hU : IsOpen {y : B | v y < v (uniformTilt.coeff p B 0 (a + b))} :=
      (Valuation.isContinuous_def.mp hv) _
    have h0 : (0 : B) ∈ {y : B | v y < v (uniformTilt.coeff p B 0 (a + b))} := by
      simpa only [Set.mem_ofPred_eq, map_zero] using lt_of_le_of_lt zero_le hlt
    have htend : Tendsto (fun m ↦ uniformTilt.coeff p B 0 (a + b) -
        (uniformTilt.coeff p B m a + uniformTilt.coeff p B m b) ^ p ^ m) atTop (𝓝 0) := by
      simpa only [zero_add, sub_self] using
        (tendsto_const_nhds (x := uniformTilt.coeff p B 0 (a + b))).sub
          (uniformTilt.coeff_add a b 0)
    obtain ⟨m, hm⟩ := (htend.eventually (hU.mem_nhds h0)).exists
    have hm' : v (uniformTilt.coeff p B 0 (a + b) -
        (uniformTilt.coeff p B m a + uniformTilt.coeff p B m b) ^ p ^ m) <
        v (uniformTilt.coeff p B 0 (a + b)) := hm
    have hpow : v ((uniformTilt.coeff p B m a + uniformTilt.coeff p B m b) ^ p ^ m) ≤
        max (v (uniformTilt.coeff p B 0 a)) (v (uniformTilt.coeff p B 0 b)) := by
      rw [map_pow]
      have ha_pow : v (uniformTilt.coeff p B m a) ^ p ^ m = v (uniformTilt.coeff p B 0 a) := by
        rw [← map_pow]
        simpa only [zero_add] using congrArg v (uniformTilt.coeff_pow_p_pow a 0 m)
      have hb_pow : v (uniformTilt.coeff p B m b) ^ p ^ m = v (uniformTilt.coeff p B 0 b) := by
        rw [← map_pow]
        simpa only [zero_add] using congrArg v (uniformTilt.coeff_pow_p_pow b 0 m)
      rcases le_total (v (uniformTilt.coeff p B m a)) (v (uniformTilt.coeff p B m b)) with hab | hab
      · calc v (uniformTilt.coeff p B m a + uniformTilt.coeff p B m b) ^ p ^ m
            ≤ v (uniformTilt.coeff p B m b) ^ p ^ m :=
              pow_le_pow_left' (v.map_add _ _ |>.trans (max_le hab le_rfl)) _
          _ = v (uniformTilt.coeff p B 0 b) := hb_pow
          _ ≤ max (v (uniformTilt.coeff p B 0 a))
              (v (uniformTilt.coeff p B 0 b)) := le_max_right _ _
      · calc v (uniformTilt.coeff p B m a + uniformTilt.coeff p B m b) ^ p ^ m
            ≤ v (uniformTilt.coeff p B m a) ^ p ^ m :=
              pow_le_pow_left' (v.map_add _ _ |>.trans (max_le le_rfl hab)) _
          _ = v (uniformTilt.coeff p B 0 a) := ha_pow
          _ ≤ max (v (uniformTilt.coeff p B 0 a)) (v (uniformTilt.coeff p B 0 b)) := le_max_left _ _
    have hmax : v (uniformTilt.coeff p B 0 (a + b)) ≤
        max (v (uniformTilt.coeff p B 0 (a + b) -
            (uniformTilt.coeff p B m a + uniformTilt.coeff p B m b) ^ p ^ m))
          (v ((uniformTilt.coeff p B m a + uniformTilt.coeff p B m b) ^ p ^ m)) := by
      simpa only [sub_add_cancel] using v.map_add
        (uniformTilt.coeff p B 0 (a + b) -
          (uniformTilt.coeff p B m a + uniformTilt.coeff p B m b) ^ p ^ m)
        ((uniformTilt.coeff p B m a + uniformTilt.coeff p B m b) ^ p ^ m)
    exact lt_irrefl _ (hmax.trans_lt (max_lt hm' (hpow.trans_lt hlt)))

private theorem sharpValuation_isContinuous {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation B Γ₀) (hv : v.IsContinuous) :
    (sharpValuation (p := p) v hv).IsContinuous := by
  rw [Valuation.isContinuous_def]
  intro b
  exact ((Valuation.isContinuous_def.mp hv) (uniformTilt.coeff p B 0 b)).preimage
    (uniformTilt.continuous_coeff 0)

open scoped Classical in
/-- If a finite subset `T` of `B♭` contains a unit, then the sharp images of elements of `T`
generate the unit ideal of `B` (and hence an open ideal). -/
theorem span_image_coeff_zero_eq_top_of_exists_isUnit (T : Finset (uniformTilt p B))
    (hT : ∃ f ∈ T, IsUnit f) :
    Ideal.span ((T.image (uniformTilt.coeff p B 0) : Finset B) : Set B) = ⊤ := by
  obtain ⟨f, hfT, hf⟩ := hT
  refine Ideal.eq_top_of_isUnit_mem _ ?_ (uniformTilt.isUnit_iff_coeff_zero.mp hf)
  exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hfT))

open scoped Classical in
/-- If a finite subset `T` of `B♭` contains a unit, then `T♯` generates an open ideal of `B`. -/
theorem isOpen_span_image_coeff_zero_of_exists_isUnit (T : Finset (uniformTilt p B))
    (hT : ∃ f ∈ T, IsUnit f) :
    IsOpen ((Ideal.span ((T.image (uniformTilt.coeff p B 0) : Finset B) : Set B) : Ideal B) :
      Set B) := by
  rw [span_image_coeff_zero_eq_top_of_exists_isUnit T hT]
  exact isOpen_univ

variable [IsTateRing (uniformTilt p B)]

/-- **The tilting map on adic spectra** `Spa(B, B⁺) → Spa(B♭, B♭⁺)`: sends a point `x` to the
point `x♭` whose underlying valuation is `v_x ∘ ♯` (Scholze, *Perfectoid spaces*, Theorem 6.3;
Kedlaya, *AWS 2017*, Lemma 2.6.12). -/
noncomputable def spaTilt (P : Pair B) (x : spa P.plus) : spa (P.tilt (p := p)).plus :=
  ⟨ofValuation (sharpValuation x.1.valuation
      ((isContinuous_def x.1).mp ((mem_spa_iff P.plus x.1).mp x.2).1)),
    (mem_spa_iff _ _).mpr
      ⟨(isContinuous_ofValuation_iff _).mpr
          (sharpValuation_isContinuous x.1.valuation
            ((isContinuous_def x.1).mp ((mem_spa_iff P.plus x.1).mp x.2).1)),
        fun a ha ↦ by
          rw [vle_ofValuation]
          change x.1.valuation (uniformTilt.coeff p B 0 a) ≤
            x.1.valuation (uniformTilt.coeff p B 0 1)
          rw [valuation_le_iff, map_one]
          rw [Pair.tilt_plus] at ha
          exact ((mem_spa_iff P.plus x.1).mp x.2).2 _
            (uniformTilt.mem_plusSubring_iff_coeff_zero.mp ha)⟩⟩

/-- **Characterisation of `spaTilt`**: `(spaTilt P x)(f) ≤ (spaTilt P x)(g)` iff `x(f♯) ≤ x(g♯)`. -/
@[simp]
theorem spaTilt_vle_iff (P : Pair B) (x : spa P.plus) (f g : uniformTilt p B) :
    (spaTilt (p := p) P x).1.toValuativeRel.vle f g ↔
      x.1.toValuativeRel.vle (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g) := by
  rw [spaTilt, vle_ofValuation]
  change x.1.valuation (uniformTilt.coeff p B 0 f) ≤
    x.1.valuation (uniformTilt.coeff p B 0 g) ↔ _
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
    y = spaTilt (p := p) P x :=
  Subtype.ext (ValuationSpectrum.ext' fun f g ↦ (h f g).trans (spaTilt_vle_iff P x f g).symm)

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

open scoped Classical in
/-- Preimage of a basic open `spaBasicOpen` under `spaTilt`. -/
theorem spaTilt_preimage_spaBasicOpen (P : Pair B) (T : Finset (uniformTilt p B))
    (s : uniformTilt p B) :
    spaTilt (p := p) P ⁻¹' ((spaBasicOpen (P.tilt (p := p)).plus T s :
        TopologicalSpace.Opens ↥(spa (P.tilt (p := p)).plus)) :
          Set ↥(spa (P.tilt (p := p)).plus)) =
      ((spaBasicOpen P.plus (T.image (uniformTilt.coeff p B 0)) (uniformTilt.coeff p B 0 s) :
        TopologicalSpace.Opens ↥(spa P.plus)) : Set ↥(spa P.plus)) := by
  ext x
  simp only [Set.mem_preimage, SetLike.mem_coe, mem_spaBasicOpen, mem_rationalSubset_iff,
    Subtype.coe_prop, true_and, spaTilt_vle_iff, uniformTilt.coeff_zero, Finset.mem_image,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

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
/-- Every rational subset of `Spa(B♭, B♭⁺)` with open numerator ideal has a presentation
`R((insert (ϖ ^ N) T) / s)` with all elements of `T` and `s` in `B♭⁺` and a power of a given
pseudouniformiser `ϖ` among its numerators. -/
theorem exists_rationalSubset_eq_insert_pseudoUniformizer_pow_tilt (P : Pair B)
    {ϖ : uniformTilt p B} (hϖ : IsPseudoUniformizer ϖ) (T₀ : Finset (uniformTilt p B))
    (s₀ : uniformTilt p B)
    (hT₀ : IsOpen ((Ideal.span (T₀ : Set (uniformTilt p B)) : Ideal (uniformTilt p B)) :
      Set (uniformTilt p B))) :
    ∃ (N : ℕ) (T : Finset (uniformTilt p B)) (s : uniformTilt p B),
      (∀ f ∈ T, f ∈ (P.tilt (p := p)).plus) ∧ s ∈ (P.tilt (p := p)).plus ∧
      rationalSubset (P.tilt (p := p)).plus T₀ s₀ =
        rationalSubset (P.tilt (p := p)).plus (insert (ϖ ^ N) T) s :=
  ValuationSpectrum.exists_rationalSubset_eq_insert_pseudoUniformizer_pow (P.tilt (p := p)).plus
    (P.tilt (p := p)).isRingOfIntegralElements.isOpen hϖ T₀ s₀ hT₀

open scoped Classical in
/-- Specialization of `exists_rationalSubset_eq_insert_pseudoUniformizer_pow_tilt` to the tilt
`ϖ.toTilt` of a compatible-root pseudouniformiser `ϖ : PseudoUniformizerRoots p B`. -/
theorem exists_rationalSubset_eq_insert_pseudoUniformizerRoots_pow_tilt (P : Pair B)
    (ϖ : PseudoUniformizerRoots p B) (T₀ : Finset (uniformTilt p B)) (s₀ : uniformTilt p B)
    (hT₀ : IsOpen ((Ideal.span (T₀ : Set (uniformTilt p B)) : Ideal (uniformTilt p B)) :
      Set (uniformTilt p B))) :
    ∃ (N : ℕ) (T : Finset (uniformTilt p B)) (s : uniformTilt p B),
      (∀ f ∈ T, f ∈ (P.tilt (p := p)).plus) ∧ s ∈ (P.tilt (p := p)).plus ∧
      rationalSubset (P.tilt (p := p)).plus T₀ s₀ =
        rationalSubset (P.tilt (p := p)).plus (insert (ϖ.toTilt ^ N) T) s :=
  exists_rationalSubset_eq_insert_pseudoUniformizer_pow_tilt P ϖ.isPseudoUniformizer_toTilt T₀ s₀
    hT₀

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
  refine (spaTilt_eq_of_vle_iff (p := p) P fun f g ↦ ?_).symm
  rw [Pair.Hom.spaComap_val, Pair.Hom.spaComap_val, comap_vle, comap_vle,
    spaTilt_vle_iff, Pair.Hom.toRingHom_tilt, uniformTilt.coeff_map, uniformTilt.coeff_map]

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

/-- The characteristic-`p` self-identification `uniformTilt.equivOfCharP p B` as a morphism of
Huber pairs `(B♭, B♭⁺) → (B, B⁺)`. -/
noncomputable def charPTiltPairHom (P : Pair B) : Pair.Hom (P.tilt (p := p)) P where
  toRingHom := (uniformTilt.equivOfCharP p B).toRingHom
  continuous_toRingHom := uniformTilt.continuous_equivOfCharP p B
  map_mem_plus _ hx := by
    rw [Pair.tilt_plus] at hx
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, uniformTilt.equivOfCharP_apply]
    exact uniformTilt.mem_plusSubring_iff_coeff_zero.mp hx

/-- The inverse of `charPTiltPairHom` as a morphism of Huber pairs `(B, B⁺) → (B♭, B♭⁺)`. -/
noncomputable def charPTiltPairHomSymm (P : Pair B) : Pair.Hom P (P.tilt (p := p)) where
  toRingHom := (uniformTilt.equivOfCharP p B).symm.toRingHom
  continuous_toRingHom := uniformTilt.continuous_equivOfCharP_symm p B
  map_mem_plus _ hx := by
    rw [Pair.tilt_plus, uniformTilt.mem_plusSubring_iff_coeff_zero, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, ← uniformTilt.equivOfCharP_apply, RingEquiv.apply_symm_apply]
    exact hx

/-- **In characteristic `p`, `spaTilt` is the pullback along `uniformTilt.equivOfCharP`**:
specifically `spaTilt P = (charPTiltPairHom P).spaComap`. -/
theorem spaTilt_eq_spaComap_of_charP (P : Pair B) :
    spaTilt (p := p) P = (charPTiltPairHom P).spaComap := by
  funext x
  refine (spaTilt_eq_of_vle_iff (p := p) P fun f g ↦ ?_).symm
  rw [Pair.Hom.spaComap_val, comap_vle]
  simp [charPTiltPairHom]

/-- Under the characteristic-`p` identification `(equivOfCharP p B).symm`, `spaTilt` cancels to
the identity on `spa P.plus`, pointwise. -/
@[simp]
theorem spaComap_symm_spaTilt_of_charP (P : Pair B) (x : spa P.plus) :
    (charPTiltPairHomSymm (p := p) P).spaComap (spaTilt (p := p) P x) = x := by
  apply Subtype.ext
  apply ValuationSpectrum.ext'
  intro f g
  rw [Pair.Hom.spaComap_val, comap_vle, spaTilt_vle_iff]
  simp [charPTiltPairHomSymm]

/-- Under the characteristic-`p` identification `(equivOfCharP p B).symm`, `spaTilt` cancels to
the identity on `spa P.plus`. -/
@[simp]
theorem spaComap_symm_comp_spaTilt_of_charP (P : Pair B) :
    (charPTiltPairHomSymm (p := p) P).spaComap ∘ spaTilt (p := p) P = id :=
  funext (spaComap_symm_spaTilt_of_charP P)

/-- Under the characteristic-`p` identification `(equivOfCharP p B).symm`, `spaTilt` has right
inverse `(charPTiltPairHomSymm P).spaComap`, pointwise. -/
@[simp]
theorem spaTilt_spaComap_symm_of_charP (P : Pair B) (y : spa (P.tilt (p := p)).plus) :
    spaTilt (p := p) P ((charPTiltPairHomSymm (p := p) P).spaComap y) = y := by
  refine (spaTilt_eq_of_vle_iff (p := p) P fun f g ↦ ?_).symm
  rw [Pair.Hom.spaComap_val, comap_vle]
  simp [charPTiltPairHomSymm]

/-- Under the characteristic-`p` identification `(equivOfCharP p B).symm`, `spaTilt` has right
inverse `(charPTiltPairHomSymm P).spaComap`. -/
@[simp]
theorem spaTilt_comp_spaComap_symm_of_charP (P : Pair B) :
    spaTilt (p := p) P ∘ (charPTiltPairHomSymm (p := p) P).spaComap = id :=
  funext (spaTilt_spaComap_symm_of_charP P)

end CharP

end TauCeti.PerfectoidSpace
