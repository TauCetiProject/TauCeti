/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.PseudoUniformizer
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Pair
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Valuation

/-!
# The tilting map on adic spectra

Let `B` be a complete Hausdorff uniform Tate ring in which `p` is topologically nilpotent, with tilt
`B♭ = uniformTilt p B`, and let `B⁺ ⊆ B°` be a ring of integral elements (`h :
IsRingOfIntegralElements B⁺`) with integral tilt `B♭⁺ = uniformTilt.plusSubring p h`.

Although the sharp map `♯ = uniformTilt.coeff p B 0 : B♭ →* B` is only multiplicative and not a ring
homomorphism (so `(B, B⁺)` and `(B♭, B♭⁺)` are not directly linked by a morphism of Huber pairs in
mixed characteristic), pulling continuous valuations back along `♯` via
`TauCeti.Perfectoid.uniformTilt.comapValuation` defines a continuous map of adic spectra

```text
spaTilt p h : Spa(B, B⁺) → Spa(B♭, B♭⁺),   x ↦ x♭,   (x♭)(f) = x(f♯).
```

This file constructs `spaTilt` (together with its plus-free counterpart `contTilt` on `Cont B` and
the bundled `Huber.Pair.spaTilt` on Huber pairs) and establishes its foundational topological,
valuation-theoretic, and functorial properties prior to rational localisation and the tilting
homeomorphism:

* **Comparisons and uniqueness** (`spaTilt_vle_iff`, `spaTilt_vlt_iff`, `eq_spaTilt_iff`): `spaTilt
  p h x` is the unique point `y ∈ Spa(B♭, B♭⁺)` satisfying `y.vle f g ↔ x.vle f♯ g♯` for all
  `f, g : B♭`.
* **Support** (`supp_spaTilt`, `mem_supp_spaTilt_iff`): the prime ideal `supp (x♭)` has underlying
  set `♯ ⁻¹' (supp x)`.
* **Continuity** (`continuous_spaTilt`, `continuous_contTilt`): `spaTilt p h` is continuous without
  assuming `B♭` is Tate, because the preimage of every ambient basic open `Spv(B♭)(f/s)` is
  `Spv(B)(f♯/s♯)`.
* **Preimages of rational subsets and normalised presentations**
  (`spaTilt_preimage_rationalSubset`,
  `spaTilt_preimage_rationalSubset_mem_spaRationalFamily_of_exists_isUnit`,
  `exists_rationalSubset_eq_insert_pseudoUniformizer_pow`,
  `spaTilt_preimage_mem_spaRationalFamily`): set-theoretically, the preimage of `R(T/s)` under
  `spaTilt` is always `R(T♯/s♯)`. Because `♯` is multiplicative, `T♯` spans the unit ideal of `B`
  whenever `T` contains a unit of `B♭`. When `B♭` is Tate (with pseudouniformiser `ϖ♭`), every
  rational open of `Spa(B♭, B♭⁺)` admits a normalised presentation `R((T ∪ {ϖ♭ ^ N}) / s)` with
  `T ⊆ B♭⁺`, `ϖ♭ ^ N ∈ B♭⁺`, and `s ∈ B♭⁺`, so *every* rational subset of `Spa(B♭, B♭⁺)` pulls back
  under `spaTilt` to a rational subset of `Spa(B, B⁺)`.
* **Functoriality** (`spaTilt_comp_valuationSpectrumSpaComap`,
  `Huber.Pair.Hom.spaTilt_comp_spaComap`, `Huber.Pair.Hom.spaTilt_spaComap`): `spaTilt` commutes
  with `spaComap` along continuous plus-preserving ring homomorphisms and morphisms of Huber pairs.
* **Characteristic-`p` self-identification** (`spaTilt_eq_spaComap_equivOfCharP`,
  `spaTilt_eq_id_of_charP`, `spaTiltHomeomorphOfCharP`, `isHomeomorph_spaTilt_of_charP`): when `B`
  is perfect of characteristic `p`, `spaTilt` coincides with pullback along
  `uniformTilt.equivOfCharP p B : B♭ ≃+* B` and composes with the inverse identification to the
  identity, making it a homeomorphism.

No perfectoid base field, perfectoidness of `B` itself, or nontriviality of `B` is assumed.

## Main definitions

* `TauCeti.PerfectoidSpace.contTilt p` : the continuous map `Cont B → Cont B♭` sending `v` to
  `v ∘ ♯`.
* `TauCeti.PerfectoidSpace.spaTilt p h` : the tilting map `Spa(B, B⁺) → Spa(B♭, B♭⁺)`.
* `TauCeti.Huber.Pair.spaTilt p P` : the bundled tilting map `Spa(P) → Spa(P.tilt)` for a Huber
  pair `P` when `B♭` is Tate.
* `TauCeti.PerfectoidSpace.spaTiltHomeomorphOfCharP p h` : `spaTilt` packaged as a homeomorphism
  when `B` is perfect of characteristic `p`.

## Main results

* `TauCeti.PerfectoidSpace.spaTilt_vle_iff`, `TauCeti.PerfectoidSpace.spaTilt_vlt_iff`,
  `TauCeti.PerfectoidSpace.eq_spaTilt_iff`
* `TauCeti.PerfectoidSpace.supp_spaTilt`, `TauCeti.PerfectoidSpace.mem_supp_spaTilt_iff`
* `TauCeti.PerfectoidSpace.continuous_spaTilt`
* `TauCeti.PerfectoidSpace.spaTilt_preimage_rationalSubset`,
  `TauCeti.PerfectoidSpace.exists_rationalSubset_eq_insert_pseudoUniformizer_pow`,
  `TauCeti.PerfectoidSpace.spaTilt_preimage_mem_spaRationalFamily`
* `TauCeti.PerfectoidSpace.spaTilt_comp_valuationSpectrumSpaComap`,
  `TauCeti.Huber.Pair.Hom.spaTilt_comp_spaComap`, `TauCeti.Huber.Pair.Hom.spaTilt_spaComap`
* `TauCeti.PerfectoidSpace.spaTilt_eq_id_of_charP`,
  `TauCeti.PerfectoidSpace.isHomeomorph_spaTilt_of_charP`

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), Lemma 6.2 and Theorem 6.3.
* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, Lemma 3.16 and Theorem 3.17.
* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*, in
  *Perfectoid Spaces: Lectures from the 2017 Arizona Winter School*, §2.7.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  Theorem 3.6.5.
-/

public section

open Set Topology TauCeti.Huber TauCeti.Perfectoid TauCeti.ValuationSpectrum

namespace TauCeti.PerfectoidSpace

variable {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]

/-! ### Tilting on `Cont` -/

variable (p) in
/-- **The tilting map on continuous valuations `Cont B → Cont B♭`**, sending a continuous point `x`
to the point represented by `x.valuation ∘ ♯` (`uniformTilt.comapValuation`). No plus subring is
involved. -/
noncomputable def contTilt (x : cont B) : cont (uniformTilt p B) :=
  ⟨ofValuation
      (uniformTilt.comapValuation p ((isContinuous_def x.1).mp ((mem_cont_iff x.1).mp x.2))),
    (mem_cont_iff _).mpr ((isContinuous_ofValuation_iff _).mpr
      (uniformTilt.isContinuous_comapValuation _))⟩

/-- `contTilt` compares elements of `B♭` by applying `x` to their zeroth coordinates. -/
@[simp]
theorem contTilt_vle_iff (x : cont B) (f g : uniformTilt p B) :
    (contTilt p x).1.toValuativeRel.vle f g ↔
      x.1.toValuativeRel.vle (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g) := by
  rw [contTilt, vle_ofValuation, uniformTilt.comapValuation_apply,
    uniformTilt.comapValuation_apply, valuation_le_iff]

/-- Strict comparison under `contTilt` is strict comparison of zeroth coordinates. -/
@[simp]
theorem contTilt_vlt_iff (x : cont B) (f g : uniformTilt p B) :
    (contTilt p x).1.toValuativeRel.vlt f g ↔
      x.1.toValuativeRel.vlt (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g) := by
  rw [← valuation_lt_iff, ← valuation_lt_iff, ← not_le, ← not_le, valuation_le_iff,
    valuation_le_iff, contTilt_vle_iff]

/-- On a point presented as `ofValuation v`, `contTilt` is `ofValuation (comapValuation p hv)`. -/
theorem contTilt_ofValuation {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation B Γ₀) (hv : v.IsContinuous) :
    (contTilt p ⟨ofValuation v, (mem_cont_iff _).mpr ((isContinuous_ofValuation_iff v).mpr hv)⟩).1 =
      ofValuation (uniformTilt.comapValuation p hv) := by
  refine ValuationSpectrum.ext' fun f g ↦ ?_
  rw [contTilt_vle_iff, vle_ofValuation, vle_ofValuation, uniformTilt.comapValuation_apply,
    uniformTilt.comapValuation_apply]

variable (p) in
/-- `contTilt` is continuous: the preimage of `Spv(B♭)(f/s)` is `Spv(B)(f♯/s♯)`. -/
@[fun_prop, continuity]
theorem continuous_contTilt : Continuous (contTilt p (B := B)) := by
  rw [continuous_induced_rng]
  refine continuous_generateFrom_iff.mpr ?_
  rintro _ ⟨f, s, rfl⟩
  have hpre : (Subtype.val ∘ contTilt p (B := B)) ⁻¹' basicOpen f s =
      Subtype.val ⁻¹' basicOpen (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 s) := by
    ext x
    simp
  rw [hpre]
  exact (isOpen_basicOpen _ _).preimage continuous_subtype_val

/-! ### The tilting map `spaTilt` on `Spa` -/

variable (p) in
/-- **The tilting map on adic spectra** `Spa(B, B⁺) → Spa(B♭, B♭⁺)`, sending `x` to `x♭` with
`(x♭)(f) = x(f♯)` (Scholze, *Perfectoid spaces*, Lemma 6.2 and Theorem 6.3). For a bundled Huber
pair `P : Huber.Pair B` when `B♭` is Tate, see `TauCeti.Huber.Pair.spaTilt`. -/
noncomputable def spaTilt {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus)
    (x : spa Bplus) : spa (uniformTilt.plusSubring p h) := by
  refine ⟨(contTilt p ⟨x.1, (spa_def Bplus ▸ Set.inter_subset_left) x.2⟩).1, ?_⟩
  rw [mem_spa_iff]
  refine ⟨(mem_cont_iff _).mp (contTilt p _).2, fun f hf ↦ ?_⟩
  rw [contTilt_vle_iff, map_one]
  exact ((mem_spa_iff Bplus x.1).mp x.2).2 _ (uniformTilt.mem_plusSubring_iff_coeff_zero.mp hf)

/-- The underlying point of `spaTilt p h x` in `Spv B♭` agrees with `contTilt` on `x`. -/
theorem spaTilt_val_eq_contTilt_val {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus)
    (x : spa Bplus) :
    (spaTilt p h x).1 = (contTilt p ⟨x.1, (spa_def Bplus ▸ Set.inter_subset_left) x.2⟩).1 :=
  (rfl)

/-- **`spaTilt` compares elements via `♯`**: `(x♭).vle f g ↔ x.vle f♯ g♯`. -/
@[simp]
theorem spaTilt_vle_iff {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus)
    (x : spa Bplus) (f g : uniformTilt p B) :
    (spaTilt p h x).1.toValuativeRel.vle f g ↔
      x.1.toValuativeRel.vle (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g) :=
  contTilt_vle_iff ⟨x.1, (spa_def Bplus ▸ Set.inter_subset_left) x.2⟩ f g

/-- **Strict comparison under `spaTilt`**: `(x♭).vlt f g ↔ x.vlt f♯ g♯`. -/
@[simp]
theorem spaTilt_vlt_iff {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus)
    (x : spa Bplus) (f g : uniformTilt p B) :
    (spaTilt p h x).1.toValuativeRel.vlt f g ↔
      x.1.toValuativeRel.vlt (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g) :=
  contTilt_vlt_iff ⟨x.1, (spa_def Bplus ▸ Set.inter_subset_left) x.2⟩ f g

/-- **Unique characterisation of `spaTilt` by its valuative comparisons.** A point
`y ∈ Spa(B♭, B♭⁺)` equals `spaTilt p h x` if and only if `y.vle f g ↔ x.vle f♯ g♯` for all
`f, g : B♭`. -/
theorem eq_spaTilt_iff {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus)
    {x : spa Bplus} {y : spa (uniformTilt.plusSubring p h)} :
    y = spaTilt p h x ↔ ∀ f g : uniformTilt p B,
      y.1.toValuativeRel.vle f g ↔
        x.1.toValuativeRel.vle (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g) := by
  refine ⟨fun hy f g ↦ hy ▸ spaTilt_vle_iff h x f g, fun hfg ↦ Subtype.ext ?_⟩
  exact ValuationSpectrum.ext' fun f g ↦ (hfg f g).trans (spaTilt_vle_iff h x f g).symm

/-- An element `f : B♭` lies in the support of `spaTilt p h x` iff `f♯` lies in the support of `x`.
Not `@[simp]`, because `ValuationSpectrum.mem_supp_iff` already unfolds `f ∈ v.supp` to `v.vle f 0`,
which `spaTilt_vle_iff` reduces. -/
theorem mem_supp_spaTilt_iff {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus)
    (x : spa Bplus) (f : uniformTilt p B) :
    f ∈ (spaTilt p h x).1.supp ↔ uniformTilt.coeff p B 0 f ∈ x.1.supp := by
  rw [mem_supp_iff, mem_supp_iff, spaTilt_vle_iff, uniformTilt.coeff_zero]

/-- **The support of `spaTilt p h x` is the preimage under `♯` of the support of `x`.** -/
@[simp]
theorem supp_spaTilt {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus) (x : spa Bplus) :
    ((spaTilt p h x).1.supp : Set (uniformTilt p B)) =
      uniformTilt.coeff p B 0 ⁻¹' (x.1.supp : Set B) :=
  Set.ext (mem_supp_spaTilt_iff h x)

variable (p) in
/-- **Continuity of `spaTilt`.** No Tate hypothesis on `B♭` is required: the subspace topology on
`Spa(B♭, B♭⁺)` is induced from the basic opens `Spv(B♭)(f/s)`, whose preimages under `spaTilt` are
the traces of `Spv(B)(f♯/s♯)`. -/
@[fun_prop, continuity]
theorem continuous_spaTilt {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus) :
    Continuous (spaTilt p h) := by
  rw [continuous_induced_rng]
  exact (continuous_subtype_val.comp
    ((continuous_contTilt p).comp (continuous_subtype_val.subtype_mk _))).congr fun _ ↦ rfl

/-! ### Preimages of rational subsets and normalised presentations -/

open scoped Classical in
/-- If `T` contains a unit of `B♭`, then `T.image ♯` generates the unit ideal of `B`: `♯` is a
monoid homomorphism and so carries units to units. -/
theorem span_image_coeff_zero_eq_top_of_exists_isUnit {T : Finset (uniformTilt p B)}
    (hT : ∃ u ∈ T, IsUnit u) :
    Ideal.span ((T.image (uniformTilt.coeff p B 0) : Finset B) : Set B) = ⊤ := by
  obtain ⟨u, huT, hu⟩ := hT
  exact Ideal.eq_top_of_isUnit_mem _
    (Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ huT)))
    (hu.map (uniformTilt.coeff p B 0))

open scoped Classical in
/-- **Preimage of a rational subset under `spaTilt`.** Set-theoretically, for *every* finite set
`T ⊆ B♭` and denominator `s : B♭`, the preimage of `R(T/s)` under `spaTilt p h` is `R(T♯/s♯)`.
When some `u ∈ T` is a unit of `B♭`, `T♯` generates the unit ideal of `B`
(`span_image_coeff_zero_eq_top_of_exists_isUnit`), so `R(T♯/s♯)` belongs to `spaRationalFamily B⁺`
(`spaTilt_preimage_rationalSubset_mem_spaRationalFamily_of_exists_isUnit`). -/
theorem spaTilt_preimage_rationalSubset {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus)
    (T : Finset (uniformTilt p B)) (s : uniformTilt p B) :
    spaTilt p h ⁻¹' (Subtype.val ⁻¹' rationalSubset (uniformTilt.plusSubring p h) T s) =
      Subtype.val ⁻¹' rationalSubset Bplus (T.image (uniformTilt.coeff p B 0))
        (uniformTilt.coeff p B 0 s) := by
  ext x
  simp

open scoped Classical in
/-- **If `T` contains a unit of `B♭`, then `spaTilt ⁻¹' R(T/s)` is a rational subset of
`Spa(B, B⁺)`.** -/
theorem spaTilt_preimage_rationalSubset_mem_spaRationalFamily_of_exists_isUnit {Bplus : Subring B}
    (h : IsRingOfIntegralElements Bplus) {T : Finset (uniformTilt p B)}
    (hT : ∃ u ∈ T, IsUnit u) (s : uniformTilt p B) :
    spaTilt p h ⁻¹' (Subtype.val ⁻¹' rationalSubset (uniformTilt.plusSubring p h) T s) ∈
      spaRationalFamily Bplus := by
  rw [spaTilt_preimage_rationalSubset]
  refine mem_spaRationalFamily_iff.mpr ⟨T.image (uniformTilt.coeff p B 0),
    uniformTilt.coeff p B 0 s, ?_, rfl⟩
  rw [span_image_coeff_zero_eq_top_of_exists_isUnit hT]
  exact isOpen_univ

section TateTilt

variable [IsTateRing (uniformTilt p B)]

open scoped Classical in
/-- **Normalised presentation of rational subsets of `Spa(B♭, B♭⁺)`** (Scholze, *Perfectoid
spaces*, proof of Theorem 6.3). For any pseudouniformiser `ϖ♭` of `B♭` (such as
`PseudoUniformizerRoots.toTilt ψ` for `ψ : PseudoUniformizerRoots p B`), every rational subset
`R(T₀/s₀)` of `Spa(B♭, B♭⁺)` with open numerator ideal equals `R((T ∪ {ϖ♭ ^ N}) / s)` for some
`T ⊆ B♭⁺`, `ϖ♭ ^ N ∈ B♭⁺`, and `s ∈ B♭⁺`. -/
theorem exists_rationalSubset_eq_insert_pseudoUniformizer_pow {Bplus : Subring B}
    (h : IsRingOfIntegralElements Bplus) {ϖ : uniformTilt p B} (hϖ : IsPseudoUniformizer ϖ)
    {T₀ : Finset (uniformTilt p B)} {s₀ : uniformTilt p B}
    (hT₀ : IsOpen (Ideal.span (T₀ : Set (uniformTilt p B)) : Set (uniformTilt p B))) :
    ∃ (T : Finset (uniformTilt p B)) (s : uniformTilt p B) (N : ℕ),
      (T : Set (uniformTilt p B)) ⊆ uniformTilt.plusSubring p h ∧
      ϖ ^ N ∈ uniformTilt.plusSubring p h ∧
      s ∈ uniformTilt.plusSubring p h ∧
      rationalSubset (uniformTilt.plusSubring p h) T₀ s₀ =
        rationalSubset (uniformTilt.plusSubring p h) (insert (ϖ ^ N) T) s :=
  exists_rationalSubset_eq_insert_pow_of_isPseudoUniformizer
    (uniformTilt.isOpen_plusSubring h) hϖ hT₀

/-- **Every rational subset of `Spa(B♭, B♭⁺)` pulls back under `spaTilt` to a rational subset of
`Spa(B, B⁺)`.** Re-presenting `U` as `R((T ∪ {ϖ♭ ^ N}) / s)` puts the unit `ϖ♭ ^ N` among the
numerators, so `spaTilt_preimage_rationalSubset_mem_spaRationalFamily_of_exists_isUnit` applies. -/
theorem spaTilt_preimage_mem_spaRationalFamily {Bplus : Subring B}
    (h : IsRingOfIntegralElements Bplus)
    {U : Set (spa (uniformTilt.plusSubring p h))}
    (hU : U ∈ spaRationalFamily (uniformTilt.plusSubring p h)) :
    spaTilt p h ⁻¹' U ∈ spaRationalFamily Bplus := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := uniformTilt p B)
  obtain ⟨T, s, N, -, -, -, rfl⟩ :=
    exists_eq_val_preimage_rationalSubset_insert_pow_of_isPseudoUniformizer
      (uniformTilt.isOpen_plusSubring h) hϖ hU
  exact spaTilt_preimage_rationalSubset_mem_spaRationalFamily_of_exists_isUnit h
    ⟨ϖ ^ N, Finset.mem_insert_self (ϖ ^ N) T, hϖ.isUnit.pow N⟩ s

end TateTilt

end TauCeti.PerfectoidSpace

/-! ### Bundled Huber-pair interface -/

namespace TauCeti.Huber.Pair

open TauCeti.Perfectoid TauCeti.PerfectoidSpace TauCeti.ValuationSpectrum

variable {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))] [IsTateRing (uniformTilt p B)]

variable (p) in
/-- **The tilting map on the adic spectrum of a Huber pair**, `Spa(P) → Spa(P.tilt)`. Because
`Pair.tilt` is not exposed across module boundaries, this bundles `PerfectoidSpace.spaTilt` so its
codomain is `spa (P.tilt (p := p)).plus` without transport. -/
noncomputable def spaTilt (P : Pair B) (x : spa P.plus) : spa (P.tilt (p := p)).plus :=
  ⟨(PerfectoidSpace.spaTilt p P.isRingOfIntegralElements x).1, by
    rw [Pair.tilt_plus]
    exact (PerfectoidSpace.spaTilt p P.isRingOfIntegralElements x).2⟩

/-- The underlying point of `P.spaTilt p x` in `Spv B♭` is that of `PerfectoidSpace.spaTilt`. -/
@[simp]
theorem spaTilt_val (P : Pair B) (x : spa P.plus) :
    (P.spaTilt p x).1 = (PerfectoidSpace.spaTilt p P.isRingOfIntegralElements x).1 :=
  (rfl)

variable (p) in
/-- `P.spaTilt p` is continuous. -/
@[fun_prop, continuity]
theorem continuous_spaTilt (P : Pair B) : Continuous (P.spaTilt p) := by
  rw [continuous_induced_rng]
  exact (continuous_subtype_val.comp
    (PerfectoidSpace.continuous_spaTilt p P.isRingOfIntegralElements)).congr fun _ ↦ rfl

open scoped Classical in
/-- The preimage of `R(T/s)` under `P.spaTilt p` is `R(T♯/s♯)`. -/
theorem spaTilt_preimage_rationalSubset (P : Pair B) (T : Finset (uniformTilt p B))
    (s : uniformTilt p B) :
    P.spaTilt p ⁻¹' (Subtype.val ⁻¹' rationalSubset (P.tilt (p := p)).plus T s) =
      Subtype.val ⁻¹' rationalSubset P.plus (T.image (uniformTilt.coeff p B 0))
        (uniformTilt.coeff p B 0 s) := by
  ext x
  simp

/-- Every rational subset of `Spa(P.tilt)` pulls back under `P.spaTilt p` to a rational subset of
`Spa(P)`. -/
theorem spaTilt_preimage_mem_spaRationalFamily (P : Pair B)
    {U : Set (spa (P.tilt (p := p)).plus)} (hU : U ∈ spaRationalFamily (P.tilt (p := p)).plus) :
    P.spaTilt p ⁻¹' U ∈ spaRationalFamily P.plus := by
  classical
  obtain ⟨T₀, s₀, hT₀, rfl⟩ := mem_spaRationalFamily_iff.mp hU
  rw [spaTilt_preimage_rationalSubset, ← PerfectoidSpace.spaTilt_preimage_rationalSubset]
  exact PerfectoidSpace.spaTilt_preimage_mem_spaRationalFamily P.isRingOfIntegralElements
    (mem_spaRationalFamily_iff.mpr ⟨T₀, s₀, hT₀, rfl⟩)

namespace Hom

variable {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
  [IsTateRing C] [CompleteSpace C] [T2Space C] [IsUniform C]
  [Fact (IsTopologicallyNilpotent (p : C))] [IsTateRing (uniformTilt p C)]

/-- **Functoriality of `spaTilt` on morphisms of Huber pairs**:
`P.spaTilt p ∘ φ.spaComap = (φ.tilt).spaComap ∘ Q.spaTilt p`. -/
theorem spaTilt_comp_spaComap {P : Pair B} {Q : Pair C} (φ : Hom P Q) :
    P.spaTilt p ∘ φ.spaComap = (φ.tilt (p := p)).spaComap ∘ Q.spaTilt p := by
  funext x
  refine Subtype.ext (ValuationSpectrum.ext' fun f g ↦ ?_)
  rw [Function.comp_apply, Function.comp_apply, Pair.spaTilt_val, spaTilt_vle_iff,
    Hom.spaComap_val, comap_vle, Hom.spaComap_val, comap_vle, Hom.toRingHom_tilt,
    Pair.spaTilt_val, spaTilt_vle_iff, uniformTilt.coeff_map, uniformTilt.coeff_map]

/-- Pointwise form of `Hom.spaTilt_comp_spaComap`. -/
@[simp]
theorem spaTilt_spaComap {P : Pair B} {Q : Pair C} (φ : Hom P Q) (x : spa Q.plus) :
    P.spaTilt p (φ.spaComap x) = (φ.tilt (p := p)).spaComap (Q.spaTilt p x) :=
  congrFun φ.spaTilt_comp_spaComap x

end Hom

end TauCeti.Huber.Pair

namespace TauCeti.PerfectoidSpace

variable {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]

/-! ### Unbundled functoriality -/

section Functoriality

variable {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
  [IsTateRing C] [CompleteSpace C] [T2Space C] [IsUniform C]
  [Fact (IsTopologicallyNilpotent (p : C))]

/-- **Unbundled naturality of `spaTilt` with respect to `ValuationSpectrum.spaComap`.** No Tate
hypothesis on `B♭` or `C♭` is needed. -/
theorem spaTilt_comp_valuationSpectrumSpaComap {Bplus : Subring B} {Cplus : Subring C}
    (hB : IsRingOfIntegralElements Bplus) (hC : IsRingOfIntegralElements Cplus)
    (φ : B →+* C) (hφ : Continuous φ) (hplus : ∀ b ∈ Bplus, φ b ∈ Cplus) :
    spaTilt p hB ∘ ValuationSpectrum.spaComap φ hφ Bplus Cplus hplus =
      ValuationSpectrum.spaComap (uniformTilt.map φ hφ) (uniformTilt.continuous_map φ hφ)
        (uniformTilt.plusSubring p hB) (uniformTilt.plusSubring p hC)
        (fun _ hx ↦ uniformTilt.map_mem_plusSubring φ hφ hplus hx) ∘ spaTilt p hC := by
  funext x
  rw [Function.comp_apply, Function.comp_apply]
  symm
  refine (eq_spaTilt_iff hB).mpr fun f g ↦ ?_
  rw [ValuationSpectrum.spaComap_val, comap_vle,
    spaTilt_vle_iff, uniformTilt.coeff_map, uniformTilt.coeff_map,
    ValuationSpectrum.spaComap_val, comap_vle]

end Functoriality

/-! ### Self-identification in characteristic `p` -/

section CharP

variable [CharP B p] [PerfectRing B p]

/-- **In characteristic `p`, `spaTilt` equals pullback along `uniformTilt.equivOfCharP p B`.** -/
theorem spaTilt_eq_spaComap_equivOfCharP {Bplus : Subring B}
    (h : IsRingOfIntegralElements Bplus)
    {hcont : Continuous (uniformTilt.equivOfCharP p B : uniformTilt p B →+* B)}
    {hplus : ∀ f ∈ uniformTilt.plusSubring p h,
      (uniformTilt.equivOfCharP p B : uniformTilt p B →+* B) f ∈ Bplus} :
    spaTilt p h =
      ValuationSpectrum.spaComap (uniformTilt.equivOfCharP p B : uniformTilt p B →+* B) hcont
        (uniformTilt.plusSubring p h) Bplus hplus := by
  funext x
  symm
  refine (eq_spaTilt_iff h).mpr fun f g ↦ ?_
  rw [ValuationSpectrum.spaComap_val, comap_vle, RingHom.coe_coe,
    uniformTilt.equivOfCharP_apply, uniformTilt.equivOfCharP_apply]

/-- **Under the characteristic-`p` identification of `B` with its tilt, `spaTilt` is the identity.**
Specifically, composing `spaTilt p h` with `spaComap` along `(uniformTilt.equivOfCharP p B).symm`
yields `id` on `Spa(B, B⁺)`. -/
@[simp]
theorem spaTilt_eq_id_of_charP {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus)
    {hcont : Continuous ((uniformTilt.equivOfCharP p B).symm : B →+* uniformTilt p B)}
    {hplus : ∀ b ∈ Bplus,
      ((uniformTilt.equivOfCharP p B).symm : B →+* uniformTilt p B) b ∈
        uniformTilt.plusSubring p h} :
    ValuationSpectrum.spaComap ((uniformTilt.equivOfCharP p B).symm : B →+* uniformTilt p B) hcont
        Bplus (uniformTilt.plusSubring p h) hplus ∘ spaTilt p h = _root_.id := by
  funext x
  rw [Function.comp_apply, spaTilt_eq_spaComap_equivOfCharP h
    (hcont := uniformTilt.continuous_equivOfCharP p B)
    (hplus := fun _ hf ↦ by simpa using uniformTilt.mem_plusSubring_iff_coeff_zero.mp hf)]
  exact spaComap_spaComap ((uniformTilt.equivOfCharP p B).symm : B →+* uniformTilt p B) hcont hplus
    (uniformTilt.equivOfCharP p B : uniformTilt p B →+* B)
    (uniformTilt.continuous_equivOfCharP p B)
    (uniformTilt.equivOfCharP p B).apply_symm_apply
    (fun _ hf ↦ by simpa using uniformTilt.mem_plusSubring_iff_coeff_zero.mp hf) x

/-- Pointwise form of `spaTilt_eq_id_of_charP`. -/
@[simp]
theorem spaComap_equivOfCharP_symm_spaTilt {Bplus : Subring B}
    (h : IsRingOfIntegralElements Bplus)
    {hcont : Continuous ((uniformTilt.equivOfCharP p B).symm : B →+* uniformTilt p B)}
    {hplus : ∀ b ∈ Bplus,
      ((uniformTilt.equivOfCharP p B).symm : B →+* uniformTilt p B) b ∈
        uniformTilt.plusSubring p h}
    (x : spa Bplus) :
    ValuationSpectrum.spaComap ((uniformTilt.equivOfCharP p B).symm : B →+* uniformTilt p B) hcont
        Bplus (uniformTilt.plusSubring p h) hplus (spaTilt p h x) = x :=
  congrFun (spaTilt_eq_id_of_charP h) x

/-- Composing in the opposite order also yields the identity on `Spa(B♭, B♭⁺)`. -/
@[simp]
theorem spaTilt_comp_spaComap_equivOfCharP_symm {Bplus : Subring B}
    (h : IsRingOfIntegralElements Bplus)
    {hcont : Continuous ((uniformTilt.equivOfCharP p B).symm : B →+* uniformTilt p B)}
    {hplus : ∀ b ∈ Bplus,
      ((uniformTilt.equivOfCharP p B).symm : B →+* uniformTilt p B) b ∈
        uniformTilt.plusSubring p h} :
    spaTilt p h ∘
      ValuationSpectrum.spaComap ((uniformTilt.equivOfCharP p B).symm : B →+* uniformTilt p B)
        hcont Bplus (uniformTilt.plusSubring p h) hplus = _root_.id := by
  funext y
  rw [Function.comp_apply, spaTilt_eq_spaComap_equivOfCharP h
    (hcont := uniformTilt.continuous_equivOfCharP p B)
    (hplus := fun _ hf ↦ by simpa using uniformTilt.mem_plusSubring_iff_coeff_zero.mp hf)]
  exact spaComap_spaComap (uniformTilt.equivOfCharP p B : uniformTilt p B →+* B)
    (uniformTilt.continuous_equivOfCharP p B)
    (fun _ hf ↦ by simpa using uniformTilt.mem_plusSubring_iff_coeff_zero.mp hf)
    ((uniformTilt.equivOfCharP p B).symm : B →+* uniformTilt p B) hcont
    (uniformTilt.equivOfCharP p B).symm_apply_apply hplus y

variable (p) in
/-- **Self-identification of `Spa(B, B⁺)` with `Spa(B♭, B♭⁺)` in characteristic `p`**, packaged as
a homeomorphism with forward map `spaTilt p h` and inverse induced by `(equivOfCharP p B).symm`. -/
noncomputable def spaTiltHomeomorphOfCharP {Bplus : Subring B}
    (h : IsRingOfIntegralElements Bplus) :
    spa Bplus ≃ₜ spa (uniformTilt.plusSubring p h) where
  toFun := spaTilt p h
  invFun := ValuationSpectrum.spaComap ((uniformTilt.equivOfCharP p B).symm : B →+* uniformTilt p B)
    (uniformTilt.continuous_equivOfCharP_symm p B) Bplus (uniformTilt.plusSubring p h)
    (fun b hb ↦ by simp [hb])
  left_inv := congrFun (spaTilt_eq_id_of_charP h)
  right_inv := congrFun (spaTilt_comp_spaComap_equivOfCharP_symm h)
  continuous_toFun := continuous_spaTilt p h
  continuous_invFun := ValuationSpectrum.continuous_spaComap _ _ _ _ _

/-- **In characteristic `p`, `spaTilt` is already a homeomorphism.** -/
theorem isHomeomorph_spaTilt_of_charP {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus) :
    IsHomeomorph (spaTilt p h) :=
  (spaTiltHomeomorphOfCharP p h).isHomeomorph

end CharP

end TauCeti.PerfectoidSpace
