/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.MorphismSpectral
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.PseudoUniformizer
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Gauge
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Pair
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Valuation

/-!
# The tilting map on adic spectra

Let `B` be a complete Hausdorff uniform Tate ring in which `p` is topologically nilpotent, with
tilt `B♭ = uniformTilt p B` and sharp map `♯ = uniformTilt.coeff p B 0 : B♭ →* B`. Although `♯` is
not a ring homomorphism (so `ValuationSpectrum.comap` does not apply to it), pulling a continuous
valuation `v` on `B` back along `♯` produces a continuous valuation `uniformTilt.comapSharp hv` on
`B♭`.

Passing to valuation equivalence classes gives a continuous map on spaces of continuous valuations
```text
contTilt p B : cont B → cont (uniformTilt p B),
```
without assuming that `B♭` is Tate. When `B♭` is Tate and `P : Huber.Pair B` is a Huber pair on `B`
with tilted pair `P.tilt : Huber.Pair B♭`, `contTilt` restricts to the **tilting map on adic
spectra**
```text
spaTilt p P : spa P.plus → spa (P.tilt (p := p)).plus,
```
uniquely characterised on comparisons by
`(spaTilt p P x).1.toValuativeRel.vle f g ↔ x.1.toValuativeRel.vle (f♯) (g♯)`.

Because `B♭` is Tate, every rational open `U ∈ spaRationalFamily (P.tilt).plus` admits an integral
presentation `R((insert (ψ ^ N) T) / s)` containing a unit power `ψ ^ N` of a pseudouniformiser of
`B♭` among its numerators (`exists_mem_spaRationalFamily_eq_insert_pseudoUniformizer_pow`). Since
`♯` preserves units, the image numerator set `(insert (ψ ^ N) T).image ♯` contains the unit
`(ψ ^ N)♯` and therefore generates the unit ideal of `B`. Consequently, `spaTilt p P` pulls every
rational open of `Spa(P.tilt)` back to a rational open of `Spa(P)`, and is in particular a
spectral map.

On a perfect ring `B` of characteristic `p`, `♯` coincides with the ring isomorphism
`uniformTilt.equivOfCharP p B`, so `spaTilt p P` coincides with `(P.tiltEquivHom).spaComap` and is a
homeomorphism with inverse `(P.tiltEquivSymmHom).spaComap`.

## Main definitions

* `TauCeti.PerfectoidSpace.contTilt`: the map `cont B → cont (uniformTilt p B)` sending `[v]` to
  `[v ∘ ♯]`.
* `TauCeti.PerfectoidSpace.spaTilt`: the tilting map `spa P.plus → spa (P.tilt (p := p)).plus` for
  a Huber pair `P : Huber.Pair B` whose tilt is Tate.
* `TauCeti.PerfectoidSpace.spaTiltHomeomorphOfCharP`: the homeomorphism
  `spa P.plus ≃ₜ spa (P.tilt (p := p)).plus` promoted from `spaTilt` when `B` is perfect of
  characteristic `p`.

## Main results

* `TauCeti.PerfectoidSpace.spaTilt_vle_iff`, `spaTilt_vlt_iff`, `spaTilt_eq_iff_forall_vle`:
  characterisation of `spaTilt p P x` by sharp comparisons.
* `TauCeti.PerfectoidSpace.supp_spaTilt`, `mem_supp_spaTilt_iff`: the support of `spaTilt p P x` is
  the preimage of `x.1.supp` under `♯`.
* `TauCeti.PerfectoidSpace.continuous_contTilt`, `continuous_spaTilt`: continuity of the tilting
  maps.
* `TauCeti.PerfectoidSpace.spaTilt_preimage_rationalSubset`: preimage formula
  `spaTilt p P ⁻¹' R(T/s) = R((T.image ♯) / s♯)`.
* `TauCeti.PerfectoidSpace.exists_rationalSubset_eq_insert_pseudoUniformizer_pow`: every rational
  subset of `Spa(P.tilt)` has an integral presentation containing `(ϖ.toTilt) ^ N` among its
  numerators.
* `TauCeti.PerfectoidSpace.spaTilt_preimage_mem_spaRationalFamily`, `isSpectralMap_spaTilt`:
  preimages of rational opens under `spaTilt` are rational opens, and `spaTilt` is spectral.
* `TauCeti.PerfectoidSpace.spaTilt_comp_spaComap`, `spaTilt_spaComap`: naturality with respect to
  morphisms of Huber pairs.
* `TauCeti.PerfectoidSpace.spaTilt_eq_id_of_charP`: in characteristic `p`, composing `spaTilt p P`
  with `(P.tiltEquivSymmHom).spaComap` is the identity.

## References

* P. Scholze, *Étale cohomology of diamonds*, Theorem 3.12.
* P. Scholze, *Perfectoid spaces*, Theorem 6.3.
* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*, in
  *Perfectoid Spaces: Lectures from the 2017 Arizona Winter School*, Lemma 2.6.12 and
  Theorem 2.6.13.
* P. Scholze and J. Weinstein, *Berkeley Lectures on p-adic Geometry*, Theorem 6.2.7.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid TauCeti.ValuationSpectrum

namespace TauCeti.PerfectoidSpace

section Cont

variable (p : ℕ) [Fact p.Prime] (B : Type*) [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]

/-- **The tilting map on spaces of continuous valuations.** Sends a continuous point `v ∈ cont B`
to the class of `v.valuation ∘ ♯` in `cont (uniformTilt p B)`. No Tate hypothesis on the tilt is
needed. -/
noncomputable def contTilt (v : cont B) : cont (uniformTilt p B) :=
  ⟨ofValuation (uniformTilt.comapSharp (p := p)
      ((isContinuous_def v.1).mp ((mem_cont_iff v.1).mp v.2))),
    (mem_cont_iff _).mpr <| (isContinuous_ofValuation_iff _).mpr <|
      uniformTilt.isContinuous_comapSharp
        ((isContinuous_def v.1).mp ((mem_cont_iff v.1).mp v.2))⟩

variable {p B}

/-- `contTilt` compares elements of `B♭` by comparing their zeroth coordinates in `B`. -/
@[simp]
theorem contTilt_vle_iff (v : cont B) (f g : uniformTilt p B) :
    (contTilt p B v).1.toValuativeRel.vle f g ↔
      v.1.toValuativeRel.vle (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g) := by
  unfold contTilt
  simp only [vle_ofValuation, uniformTilt.comapSharp_apply, valuation_le_iff]

/-- Strict comparison form of `contTilt_vle_iff`. -/
@[simp]
theorem contTilt_vlt_iff (v : cont B) (f g : uniformTilt p B) :
    (contTilt p B v).1.toValuativeRel.vlt f g ↔
      v.1.toValuativeRel.vlt (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g) := by
  rw [← valuation_lt_iff, ← valuation_lt_iff, ← not_le, ← not_le, valuation_le_iff,
    valuation_le_iff, contTilt_vle_iff]

/-- `contTilt p B v` is the unique point of `cont (uniformTilt p B)` whose valuative relation pulls
back `v` along sharp. -/
theorem contTilt_eq_iff_forall_vle (v : cont B) (w : cont (uniformTilt p B)) :
    w = contTilt p B v ↔
      ∀ f g : uniformTilt p B,
        w.1.toValuativeRel.vle f g ↔
          v.1.toValuativeRel.vle (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g) := by
  refine ⟨fun h f g ↦ h ▸ contTilt_vle_iff v f g, fun h ↦ Subtype.ext (ext' fun f g ↦ ?_)⟩
  rw [h f g, contTilt_vle_iff]

/-- On a point presented by an explicit continuous valuation `w`, `contTilt` is represented by
`uniformTilt.comapSharp hw`. -/
theorem contTilt_ofValuation {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {w : Valuation B Γ₀} (hw : w.IsContinuous) :
    (contTilt p B
      ⟨ofValuation w, (mem_cont_iff _).mpr ((isContinuous_ofValuation_iff w).mpr hw)⟩).1 =
      ofValuation (uniformTilt.comapSharp (p := p) hw) := by
  refine ext' fun f g ↦ ?_
  simp

/-- An element of `B♭` lies in the support of `contTilt p B v` iff its sharp lies in `v.1.supp`.
Not `@[simp]`, since `ValuationSpectrum.mem_supp_iff` already simplifies the left-hand side. -/
theorem mem_supp_contTilt_iff (v : cont B) (f : uniformTilt p B) :
    f ∈ (contTilt p B v).1.supp ↔ uniformTilt.coeff p B 0 f ∈ v.1.supp := by
  simp

/-- As a set, the support of `contTilt p B v` is the preimage of `v.1.supp` under sharp. -/
theorem supp_contTilt (v : cont B) :
    ((contTilt p B v).1.supp : Set (uniformTilt p B)) =
      uniformTilt.coeff p B 0 ⁻¹' (v.1.supp : Set B) :=
  Set.ext (mem_supp_contTilt_iff v)

/-- The preimage under `contTilt p B` of the trace of `basicOpen f s` is the trace of
`basicOpen (f♯) (s♯)`. -/
theorem contTilt_preimage_basicOpen (f s : uniformTilt p B) :
    contTilt p B ⁻¹' (Subtype.val ⁻¹' basicOpen f s) =
      Subtype.val ⁻¹' basicOpen (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 s) := by
  ext v
  simp [mem_basicOpen_iff]

variable (p B) in
/-- `contTilt p B` is continuous for the subspace topologies inherited from `Spv`. -/
@[fun_prop, continuity]
theorem continuous_contTilt : Continuous (contTilt p B) := by
  rw [continuous_induced_rng, continuous_iff_le_induced, instTopologicalSpace_eq_generateFrom]
  apply le_induced_generateFrom
  rintro _ ⟨f, s, rfl⟩
  change IsOpen (contTilt p B ⁻¹' (Subtype.val ⁻¹' basicOpen f s))
  rw [contTilt_preimage_basicOpen]
  exact (isOpen_basicOpen _ _).preimage continuous_subtype_val

open scoped Classical in
/-- If `T : Finset B♭` contains a unit of `B♭`, then its sharp image `T.image ♯` contains a unit
of `B` and therefore generates the unit ideal of `B`. -/
theorem span_image_coeff_zero_eq_top_of_exists_isUnit {T : Finset (uniformTilt p B)}
    (hu : ∃ u ∈ T, IsUnit u) :
    Ideal.span ((T.image (uniformTilt.coeff p B 0) : Finset B) : Set B) = ⊤ := by
  obtain ⟨u, huT, hu_unit⟩ := hu
  exact Ideal.eq_top_of_isUnit_mem _
    (Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ huT)))
    (hu_unit.map (uniformTilt.coeff p B 0))

end Cont

section Spa

variable (p : ℕ) [Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]
  [IsTateRing (uniformTilt p B)]

variable {p} in
/-- `contTilt` carries points of `spa P.plus` into `spa (P.tilt).plus`. -/
theorem contTilt_mem_spa (P : Pair B) (x : spa P.plus) :
    (contTilt p B ⟨x.1, (mem_cont_iff x.1).mpr ((mem_spa_iff P.plus x.1).mp x.2).1⟩).1 ∈
      spa (P.tilt (p := p)).plus := by
  obtain ⟨hx_cont, hx_plus⟩ := (mem_spa_iff P.plus x.1).mp x.2
  rw [mem_spa_iff]
  refine ⟨(mem_cont_iff _).mp (contTilt p B ⟨x.1, (mem_cont_iff x.1).mpr hx_cont⟩).2, fun f hf ↦ ?_⟩
  rw [Pair.tilt_plus, uniformTilt.mem_plusSubring_iff_coeff_zero] at hf
  rw [contTilt_vle_iff, map_one]
  exact hx_plus _ hf

/-- **The tilting map `x ↦ x♭` on adic spectra**, from `Spa(B, B⁺)` to `Spa(B♭, B♭⁺)`, sending a
continuous valuation `v_x` to `v_x ∘ ♯`. -/
noncomputable def spaTilt (P : Pair B) (x : spa P.plus) : spa (P.tilt (p := p)).plus :=
  ⟨(contTilt p B ⟨x.1, (mem_cont_iff x.1).mpr ((mem_spa_iff P.plus x.1).mp x.2).1⟩).1,
    contTilt_mem_spa P x⟩

variable {p}

/-- The underlying point of `spaTilt p P x` in `Spv B♭` agrees with `contTilt p B`. -/
theorem spaTilt_val_eq_contTilt (P : Pair B) (x : spa P.plus) :
    (spaTilt p P x).1 =
      (contTilt p B ⟨x.1, (mem_cont_iff x.1).mpr ((mem_spa_iff P.plus x.1).mp x.2).1⟩).1 :=
  (rfl)

/-- **Defining comparison property of `spaTilt`:** `|f(x♭)| ≤ |g(x♭)| ↔ |f♯(x)| ≤ |g♯(x)|`. -/
@[simp]
theorem spaTilt_vle_iff (P : Pair B) (x : spa P.plus) (f g : uniformTilt p B) :
    (spaTilt p P x).1.toValuativeRel.vle f g ↔
      x.1.toValuativeRel.vle (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g) :=
  contTilt_vle_iff _ f g

/-- Strict comparison form of `spaTilt_vle_iff`: `|f(x♭)| < |g(x♭)| ↔ |f♯(x)| < |g♯(x)|`. -/
@[simp]
theorem spaTilt_vlt_iff (P : Pair B) (x : spa P.plus) (f g : uniformTilt p B) :
    (spaTilt p P x).1.toValuativeRel.vlt f g ↔
      x.1.toValuativeRel.vlt (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g) :=
  contTilt_vlt_iff _ f g

/-- **Uniqueness characterisation of `spaTilt`:** `spaTilt p P x` is the unique point `y` of
`spa (P.tilt).plus` satisfying `y.vle f g ↔ x.vle (f♯) (g♯)` for all `f, g : B♭`. -/
theorem spaTilt_eq_iff_forall_vle (P : Pair B) (x : spa P.plus)
    (y : spa (P.tilt (p := p)).plus) :
    y = spaTilt p P x ↔
      ∀ f g : uniformTilt p B,
        y.1.toValuativeRel.vle f g ↔
          x.1.toValuativeRel.vle (uniformTilt.coeff p B 0 f) (uniformTilt.coeff p B 0 g) := by
  refine ⟨fun h f g ↦ h ▸ spaTilt_vle_iff P x f g, fun h ↦ Subtype.ext (ext' fun f g ↦ ?_)⟩
  rw [h f g, spaTilt_vle_iff]

/-- An element `f : B♭` lies in the support of `spaTilt p P x` iff `f♯` lies in `x.1.supp`.
Not `@[simp]`, since `ValuationSpectrum.mem_supp_iff` already simplifies the left-hand side. -/
theorem mem_supp_spaTilt_iff (P : Pair B) (x : spa P.plus) (f : uniformTilt p B) :
    f ∈ (spaTilt p P x).1.supp ↔ uniformTilt.coeff p B 0 f ∈ x.1.supp := by
  simp

/-- **Support of a tilted point:** as a set, `supp (x♭) = {f ∈ B♭ | f♯ ∈ supp x}`. -/
theorem supp_spaTilt (P : Pair B) (x : spa P.plus) :
    ((spaTilt p P x).1.supp : Set (uniformTilt p B)) =
      uniformTilt.coeff p B 0 ⁻¹' (x.1.supp : Set B) :=
  Set.ext (mem_supp_spaTilt_iff P x)

variable (p) in
/-- **Continuity of the tilting map `spaTilt` on adic spectra.** -/
@[fun_prop, continuity]
theorem continuous_spaTilt (P : Pair B) : Continuous (spaTilt p P) := by
  rw [continuous_induced_rng]
  have hincl : Continuous fun x : spa P.plus ↦
      (⟨x.1, (mem_cont_iff x.1).mpr ((mem_spa_iff P.plus x.1).mp x.2).1⟩ : cont B) :=
    continuous_induced_rng.mpr continuous_subtype_val
  exact (continuous_subtype_val.comp ((continuous_contTilt p B).comp hincl)).congr fun _ ↦ rfl

open scoped Classical in
/-- **Preimage of a rational subset under `spaTilt`:** for arbitrary `T : Finset B♭` and `s : B♭`,
`spaTilt ⁻¹' R(T/s) = R((T.image ♯) / s♯)` inside `spa P.plus`. -/
theorem spaTilt_preimage_rationalSubset (P : Pair B)
    (T : Finset (uniformTilt p B)) (s : uniformTilt p B) :
    spaTilt p P ⁻¹' (Subtype.val ⁻¹' rationalSubset (P.tilt (p := p)).plus T s) =
      Subtype.val ⁻¹'
        rationalSubset P.plus (T.image (uniformTilt.coeff p B 0)) (uniformTilt.coeff p B 0 s) := by
  ext x
  simp only [Set.mem_preimage, mem_rationalSubset_iff, (spaTilt p P x).2, x.2, true_and,
    spaTilt_vle_iff, uniformTilt.coeff_zero, Finset.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

open scoped Classical in
/-- If `T : Finset B♭` contains a unit of `B♭`, then the preimage of `R(T/s)` under `spaTilt p P`
belongs to `spaRationalFamily P.plus`. -/
theorem spaTilt_preimage_rationalSubset_mem_spaRationalFamily_of_exists_isUnit (P : Pair B)
    {T : Finset (uniformTilt p B)} (hu : ∃ u ∈ T, IsUnit u) (s : uniformTilt p B) :
    spaTilt p P ⁻¹' (Subtype.val ⁻¹' rationalSubset (P.tilt (p := p)).plus T s) ∈
      spaRationalFamily P.plus := by
  rw [spaTilt_preimage_rationalSubset]
  refine mem_spaRationalFamily_iff.mpr
    ⟨T.image (uniformTilt.coeff p B 0), uniformTilt.coeff p B 0 s, ?_, rfl⟩
  rw [span_image_coeff_zero_eq_top_of_exists_isUnit hu]
  exact isOpen_univ

open scoped Classical in
/-- **Integral presentation of rational subsets of `Spa(P.tilt)` with a compatible-root parameter.**
Given `ϖ : PseudoUniformizerRoots p B` and any `T₀ : Finset B♭` generating the unit ideal of `B♭`,
`R(T₀/s₀)` equals `R((insert (ϖ.toTilt ^ N) T) / s)` for some `0 < N`, `insert (ϖ.toTilt ^ N) T`
in `(P.tilt).plus`, and `s ∈ (P.tilt).plus`. -/
theorem exists_rationalSubset_eq_insert_pseudoUniformizer_pow (P : Pair B)
    (ϖ : PseudoUniformizerRoots p B) {T₀ : Finset (uniformTilt p B)}
    (hspan : Ideal.span (T₀ : Set (uniformTilt p B)) = ⊤) (s₀ : uniformTilt p B) :
    ∃ (T : Finset (uniformTilt p B)) (s : uniformTilt p B) (N : ℕ),
      0 < N ∧
      ((insert (ϖ.toTilt ^ N) T : Finset (uniformTilt p B)) : Set (uniformTilt p B)) ⊆
        (P.tilt (p := p)).plus ∧
      s ∈ (P.tilt (p := p)).plus ∧
      rationalSubset (P.tilt (p := p)).plus (insert (ϖ.toTilt ^ N) T) s =
        rationalSubset (P.tilt (p := p)).plus T₀ s₀ :=
  ValuationSpectrum.exists_rationalSubset_eq_insert_pseudoUniformizer_pow
    (P.tilt (p := p)).isRingOfIntegralElements.isOpen ϖ.isPseudoUniformizer_toTilt hspan s₀

/-- **Every rational open of `Spa(P.tilt)` pulls back under `spaTilt p P` to a rational open of
`Spa(P)`.** Presenting the rational open with a power of a pseudouniformiser of `B♭` among its
numerators supplies the unit needed so that the sharp images span `⊤`. -/
theorem spaTilt_preimage_mem_spaRationalFamily (P : Pair B)
    {U : Set (spa (P.tilt (p := p)).plus)} (hU : U ∈ spaRationalFamily (P.tilt (p := p)).plus) :
    spaTilt p P ⁻¹' U ∈ spaRationalFamily P.plus := by
  classical
  obtain ⟨ψ, hψ⟩ := IsTateRing.exists_isPseudoUniformizer (A := uniformTilt p B)
  obtain ⟨T, s, N, -, -, -, rfl⟩ :=
    exists_mem_spaRationalFamily_eq_insert_pseudoUniformizer_pow
      (P.tilt (p := p)).isRingOfIntegralElements.isOpen hψ hU
  exact spaTilt_preimage_rationalSubset_mem_spaRationalFamily_of_exists_isUnit P
    ⟨ψ ^ N, Finset.mem_insert_self _ _, hψ.isUnit.pow N⟩ s

variable (p) in
/-- **The tilting map `spaTilt p P` is a spectral map.** Preimages of members of the rational basis
`spaRationalFamily (P.tilt).plus` lie in `spaRationalFamily P.plus` and are therefore
quasi-compact. -/
theorem isSpectralMap_spaTilt (P : Pair B) : IsSpectralMap (spaTilt p P) :=
  TauCeti.isSpectralMap_of_isTopologicalBasis
    (isTopologicalBasis_spaRationalFamily (P.tilt (p := p)).plus)
    (continuous_spaTilt p P) fun _ hU ↦
      isCompact_of_mem_spaRationalFamily (spaTilt_preimage_mem_spaRationalFamily P hU)

section Naturality

variable {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
  [IsTopologicalRing C] [IsTateRing C] [CompleteSpace C] [T2Space C] [IsUniform C]
  [Fact (IsTopologicallyNilpotent (p : C))] [IsTateRing (uniformTilt p C)]

/-- Pointwise naturality of `spaTilt` with respect to morphisms of Huber pairs. -/
@[simp]
theorem spaTilt_spaComap {P : Pair B} {Q : Pair C} (f : Pair.Hom P Q) (x : spa Q.plus) :
    spaTilt p P (f.spaComap x) = (f.tilt (p := p)).spaComap (spaTilt p Q x) := by
  symm
  refine (spaTilt_eq_iff_forall_vle (p := p) P (f.spaComap x) _).mpr fun a b ↦ ?_
  rw [Pair.Hom.spaComap_val, comap_vle, Pair.Hom.spaComap_val, comap_vle, Pair.Hom.toRingHom_tilt,
    spaTilt_vle_iff, uniformTilt.coeff_map, uniformTilt.coeff_map]

/-- **Naturality of `spaTilt`:** for a morphism `f : P → Q` of Huber pairs whose tilts are Tate,
`spaTilt p P ∘ f.spaComap = (f.tilt).spaComap ∘ spaTilt p Q`. -/
theorem spaTilt_comp_spaComap {P : Pair B} {Q : Pair C} (f : Pair.Hom P Q) :
    spaTilt p P ∘ f.spaComap = (f.tilt (p := p)).spaComap ∘ spaTilt p Q :=
  funext (spaTilt_spaComap f)

end Naturality

section CharP

variable [CharP B p] [PerfectRing B p]

/-- On a perfect ring of characteristic `p`, `spaTilt p P` agrees with `(P.tiltEquivHom).spaComap`,
since sharp is the ring isomorphism `uniformTilt.equivOfCharP p B`. -/
theorem spaTilt_eq_spaComap_tiltEquivHom (P : Pair B) :
    spaTilt p P = (P.tiltEquivHom (p := p)).spaComap := by
  funext x
  symm
  refine (spaTilt_eq_iff_forall_vle (p := p) P x _).mpr fun f g ↦ ?_
  rw [Pair.Hom.spaComap_val, comap_vle, Pair.toRingHom_tiltEquivHom]
  simp

/-- **Self-identification of `spaTilt` in characteristic `p`:** under the canonical Huber-pair
isomorphism `P.tiltEquivSymmHom : P → P.tilt`, `spaTilt p P` is the identity of `Spa(P)`. -/
@[simp]
theorem spaTilt_eq_id_of_charP (P : Pair B) :
    (P.tiltEquivSymmHom (p := p)).spaComap ∘ spaTilt p P = _root_.id := by
  rw [spaTilt_eq_spaComap_tiltEquivHom, ← Pair.Hom.spaComap_comp,
    Pair.tiltEquivHom_comp_tiltEquivSymmHom, Pair.Hom.spaComap_id]

/-- Pointwise form of `spaTilt_eq_id_of_charP`. -/
@[simp]
theorem spaComap_tiltEquivSymmHom_spaTilt (P : Pair B) (x : spa P.plus) :
    (P.tiltEquivSymmHom (p := p)).spaComap (spaTilt p P x) = x :=
  congrFun (spaTilt_eq_id_of_charP P) x

/-- Right-inverse companion to `spaTilt_eq_id_of_charP`: `spaTilt p P` after
`(P.tiltEquivSymmHom).spaComap` is the identity of `Spa(P.tilt)`. -/
@[simp]
theorem spaTilt_comp_spaComap_tiltEquivSymmHom (P : Pair B) :
    spaTilt p P ∘ (P.tiltEquivSymmHom (p := p)).spaComap = _root_.id := by
  rw [spaTilt_eq_spaComap_tiltEquivHom, ← Pair.Hom.spaComap_comp,
    Pair.tiltEquivSymmHom_comp_tiltEquivHom, Pair.Hom.spaComap_id]

/-- Pointwise form of `spaTilt_comp_spaComap_tiltEquivSymmHom`. -/
@[simp]
theorem spaTilt_spaComap_tiltEquivSymmHom (P : Pair B) (y : spa (P.tilt (p := p)).plus) :
    spaTilt p P ((P.tiltEquivSymmHom (p := p)).spaComap y) = y :=
  congrFun (spaTilt_comp_spaComap_tiltEquivSymmHom P) y

variable (p) in
/-- On a perfect ring of characteristic `p`, `spaTilt p P` promoted to a homeomorphism with inverse
`(P.tiltEquivSymmHom).spaComap`. -/
noncomputable def spaTiltHomeomorphOfCharP (P : Pair B) :
    spa P.plus ≃ₜ spa (P.tilt (p := p)).plus where
  toFun := spaTilt p P
  invFun := (P.tiltEquivSymmHom (p := p)).spaComap
  left_inv := spaComap_tiltEquivSymmHom_spaTilt P
  right_inv := spaTilt_spaComap_tiltEquivSymmHom P
  continuous_toFun := continuous_spaTilt p P
  continuous_invFun := (P.tiltEquivSymmHom (p := p)).continuous_spaComap

/-- Applying `spaTiltHomeomorphOfCharP` evaluates `spaTilt`. -/
@[simp]
theorem spaTiltHomeomorphOfCharP_apply (P : Pair B) (x : spa P.plus) :
    spaTiltHomeomorphOfCharP p P x = spaTilt p P x := (rfl)

/-- Applying the inverse of `spaTiltHomeomorphOfCharP` evaluates `(P.tiltEquivSymmHom).spaComap`. -/
@[simp]
theorem spaTiltHomeomorphOfCharP_symm_apply (P : Pair B) (y : spa (P.tilt (p := p)).plus) :
    (spaTiltHomeomorphOfCharP p P).symm y = (P.tiltEquivSymmHom (p := p)).spaComap y := (rfl)

/-- On a perfect ring of characteristic `p`, `spaTilt p P` is a homeomorphism. -/
theorem isHomeomorph_spaTilt_of_charP (P : Pair B) : IsHomeomorph (spaTilt p P) :=
  (spaTiltHomeomorphOfCharP p P).isHomeomorph

end CharP

end Spa

end TauCeti.PerfectoidSpace
