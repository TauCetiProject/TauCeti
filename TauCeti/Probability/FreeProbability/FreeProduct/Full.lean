/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.LinearAlgebra.FreeProduct.Star
public import TauCeti.Probability.FreeProbability.FreeProduct.Reduced
import TauCeti.Analysis.CStarAlgebra.Representation.GNS
import TauCeti.Analysis.CStarAlgebra.State.Spectrum
import TauCeti.Analysis.InnerProductSpace.StarAlgHom
import TauCeti.Analysis.StarAlgebra.Subrepresentation

/-!
# The full unital C⋆-free product

Let `(A i)_{i : I}` (`I : Type u`, `A : I → Type v`) be a family of unital complex C⋆-algebras.
The *universal* (or *full*) C⋆-seminorm on the algebraic star free product
`LinearAlgebra.FreeProduct ℂ A` is

`FullFreeProduct.seminorm A x = sup ‖π x‖`,

where `π` ranges over unital `⋆`-representations of `LinearAlgebra.FreeProduct ℂ A` on Hilbert
spaces `lp (fun _ : ι => ℂ) 2` indexed by types `ι : Type (max u v)`. Because every cyclic subspace
of a Hilbert-space representation of `LinearAlgebra.FreeProduct ℂ A` in any universe is isometric to
some `lp (fun _ : ι => ℂ) 2` with `ι : Type (max u v)`
(`StarAlgHom.exists_linearIsometry_mapsTo_mem_range`), this supremum dominates all Hilbert-space
representations (`FullFreeProduct.norm_representation_le_seminorm`) and hence all unital
`⋆`-homomorphisms into arbitrary unital C⋆-algebras in any universe
(`FullFreeProduct.norm_starAlgHom_le_seminorm`). On each algebraic element it is finite by
structural induction from contractivity of the factor restrictions.

Taking the C⋆-completion `TauCeti.CStarSeminorm.Completion` of `LinearAlgebra.FreeProduct ℂ A` in
the C⋆-seminorm `FullFreeProduct.seminorm A` yields the *full unital C⋆-free product*
`FullFreeProduct A`, a unital C⋆-algebra in universe `max u v`. It satisfies the coproduct universal
property `FullFreeProduct.lift : ((i : I) → A i →⋆ₐ[ℂ] B) ≃ (FullFreeProduct A →⋆ₐ[ℂ] B)` for any
unital C⋆-algebra `B` in any universe `w`.

When every factor `A i` is nontrivial, no faithful state on any `A i` is required to embed the
factors isometrically: for a given `a : A i₀`, choosing a norm-attaining state on `star a * a` at
`i₀` and arbitrary states on the remaining factors in `ReducedFreeProduct.representation` shows
`FullFreeProduct.seminorm A (ι ℂ A i₀ a) = ‖a‖`, so `FullFreeProduct.factor i₀` is isometric and
injective (`FullFreeProduct.isometry_factor`, `FullFreeProduct.factor_injective`), and
`Nontrivial (FullFreeProduct A) ↔ ∀ i, Nontrivial (A i)` (`FullFreeProduct.nontrivial_iff`).

The empty full C⋆-free product is canonically `⋆`-isomorphic to `ℂ`
(`FullFreeProduct.isEmptyEquiv`). Factorwise `⋆`-homomorphisms, index relabelings, sigma
associativity, and fiber grouping lift to `FullFreeProduct.map`, `FullFreeProduct.mapEquiv`,
`FullFreeProduct.reindexHom`, `FullFreeProduct.reindexEquiv`, `FullFreeProduct.sigmaEquiv`, and
`FullFreeProduct.fiberEquiv`. Given normalized positive functionals `φ i` on the factors,
`FullFreeProduct.toReduced φ hφ` is a surjective unital `⋆`-homomorphism onto
`ReducedFreeProduct.algebra φ hφ`, exhibiting the reduced C⋆-free product as a quotient of
`FullFreeProduct A` (`FullFreeProduct.quotientKerToReducedEquiv`) and pulling the vacuum state and
freeness of the factors back to `FullFreeProduct A`.

## Main definitions

* `TauCeti.FullFreeProduct.seminorm`: the universal C⋆-seminorm on
  `LinearAlgebra.FreeProduct ℂ A`, bundled as a `TauCeti.CStarSeminorm`.
* `TauCeti.FullFreeProduct`: the full unital C⋆-free product of `A`, a unital C⋆-algebra.
* `TauCeti.FullFreeProduct.ofAlgebraic` and `TauCeti.FullFreeProduct.factor`: the canonical dense
  unital `⋆`-homomorphism from `LinearAlgebra.FreeProduct ℂ A` and the canonical factor maps.
* `TauCeti.FullFreeProduct.liftAlgebraic`, `TauCeti.FullFreeProduct.liftRepresentation`, and
  `TauCeti.FullFreeProduct.lift`: universal properties with respect to unital C⋆-algebras and
  Hilbert-space representations in any universe.
* `TauCeti.FullFreeProduct.isEmptyEquiv`, `TauCeti.FullFreeProduct.map`,
  `TauCeti.FullFreeProduct.mapEquiv`, `TauCeti.FullFreeProduct.reindexHom`,
  `TauCeti.FullFreeProduct.reindexEquiv`, `TauCeti.FullFreeProduct.sigmaEquiv`, and
  `TauCeti.FullFreeProduct.fiberEquiv`: empty product, functoriality, relabeling, and
  associativity/grouping.
* `TauCeti.FullFreeProduct.reducedRepresentation`, `TauCeti.FullFreeProduct.toReduced`,
  `TauCeti.FullFreeProduct.quotientKerToReducedEquiv`, and `TauCeti.FullFreeProduct.state`:
  extended reduced representation, canonical quotient onto `ReducedFreeProduct.algebra φ hφ`, and
  pulled-back vacuum state.

## Main statements

* `TauCeti.FullFreeProduct.norm_representation_le_seminorm` and
  `TauCeti.FullFreeProduct.norm_starAlgHom_le_seminorm`: universe-independent upper bounds.
* `TauCeti.FullFreeProduct.seminorm_ι`, `TauCeti.FullFreeProduct.isometry_factor`, and
  `TauCeti.FullFreeProduct.factor_injective`: isometric factor embeddings for nontrivial factors
  without faithful-state hypotheses.
* `TauCeti.FullFreeProduct.nontrivial_iff`:
  `Nontrivial (FullFreeProduct A) ↔ ∀ i, Nontrivial (A i)`.
* `TauCeti.FullFreeProduct.toReduced_surjective` and
  `TauCeti.FullFreeProduct.isFreelyIndependent_factor`: surjectivity onto the reduced C⋆-free
  product and free independence of the factor ranges.

## References

* D. Voiculescu, *Symmetries of some reduced free product C⋆-algebras*, in *Operator Algebras and
  their Connections with Topology and Ergodic Theory*, Lecture Notes in Math. 1132, Springer, 1985,
  pp. 556–588.
* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, §§1.4–1.5.
* B. Blackadar, *Operator Algebras: Theory of C⋆-Algebras and von Neumann Algebras*, §II.8.3.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.4.
-/

public section

noncomputable section

open LinearAlgebra.FreeProduct
open scoped ComplexOrder InnerProductSpace

namespace TauCeti

universe u v w

section SeminormAndCompletion

variable {I : Type u} [DecidableEq I] (A : I → Type v) [∀ i, CStarAlgebra (A i)]

namespace FullFreeProduct

/-- The seminorms `x ↦ ‖π x‖` on `LinearAlgebra.FreeProduct ℂ A` induced by unital
`⋆`-representations on `ℓ²` spaces indexed in universe `max u v`. -/
private def representationSeminorms : Set (Seminorm ℂ (LinearAlgebra.FreeProduct ℂ A)) :=
  {p | ∃ (ι : Type (max u v))
    (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ]
      (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)),
      p = (normSeminorm ℂ (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)).comp
        (π : LinearAlgebra.FreeProduct ℂ A →ₗ[ℂ]
          (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2))}

/-- Every algebraic free-product element is uniformly bounded across all Hilbert-space
representations, because each factor restriction is a `⋆`-homomorphism out of a C⋆-algebra and
therefore contractive. -/
private theorem exists_representation_bound (x : LinearAlgebra.FreeProduct ℂ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type (max u v))
      (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ]
        (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)), ‖π x‖ ≤ C := by
  induction x using LinearAlgebra.FreeProduct.induction_on with
  | algebraMap r =>
    refine ⟨‖r‖, norm_nonneg r, fun ι π => ?_⟩
    rw [AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_def]
    exact (norm_smul_le r (ContinuousLinearMap.id ℂ (lp (fun _ : ι => ℂ) 2))).trans
      (mul_le_of_le_one_right (norm_nonneg r) ContinuousLinearMap.norm_id_le)
  | ι i a =>
    refine ⟨‖a‖, norm_nonneg a, fun ι π => ?_⟩
    rw [← ιStar_apply, ← StarAlgHom.comp_apply]
    exact NonUnitalStarAlgHom.norm_apply_le (π.comp (ιStar ℂ A i)).toNonUnitalStarAlgHom a
  | mul x y ihx ihy =>
    obtain ⟨Cx, hCx0, hCx⟩ := ihx
    obtain ⟨Cy, hCy0, hCy⟩ := ihy
    refine ⟨Cx * Cy, mul_nonneg hCx0 hCy0, fun ι π => ?_⟩
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (hCx ι π) (hCy ι π) (norm_nonneg _) hCx0)
  | add x y ihx ihy =>
    obtain ⟨Cx, hCx0, hCx⟩ := ihx
    obtain ⟨Cy, hCy0, hCy⟩ := ihy
    refine ⟨Cx + Cy, add_nonneg hCx0 hCy0, fun ι π => ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hCx ι π) (hCy ι π))

private theorem bddAbove_representationSeminorms : BddAbove (representationSeminorms A) := by
  rw [Seminorm.bddAbove_iff]
  choose bound _ hbound using exists_representation_bound A
  refine ⟨bound, ?_⟩
  rintro _ ⟨_, ⟨ι, π, rfl⟩, rfl⟩ x
  exact hbound x ι π

private def seminormAux : Seminorm ℂ (LinearAlgebra.FreeProduct ℂ A) :=
  sSup (representationSeminorms A)

private theorem norm_lp_le_seminormAux {A : I → Type v} [∀ i, CStarAlgebra (A i)]
    {ι : Type (max u v)}
    (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ]
      (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2))
    (x : LinearAlgebra.FreeProduct ℂ A) :
    ‖π x‖ ≤ seminormAux A x := by
  let p : Seminorm ℂ (LinearAlgebra.FreeProduct ℂ A) :=
    (normSeminorm ℂ (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)).comp
      (π : LinearAlgebra.FreeProduct ℂ A →ₗ[ℂ]
        (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2))
  have hp : p ∈ representationSeminorms A := ⟨ι, π, rfl⟩
  have hle : p ≤ seminormAux A := le_csSup (bddAbove_representationSeminorms A) hp
  exact hle x

private theorem seminormAux_le_iff_lp {A : I → Type v} [∀ i, CStarAlgebra (A i)]
    {x : LinearAlgebra.FreeProduct ℂ A} {c : ℝ} :
    seminormAux A x ≤ c ↔
      ∀ (ι : Type (max u v))
        (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ]
          (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)), ‖π x‖ ≤ c :=
  ⟨fun h ι π => (norm_lp_le_seminormAux π x).trans h, fun h => by
    rw [seminormAux, Seminorm.sSup_apply (bddAbove_representationSeminorms A)]
    have hc : 0 ≤ c := by
      let π₀ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ]
          (lp (fun _ : PEmpty.{max u v + 1} => ℂ) 2 →L[ℂ]
            lp (fun _ : PEmpty.{max u v + 1} => ℂ) 2) :=
        liftStar fun {i} =>
          { toFun _ := 0
            map_one' := Subsingleton.elim _ _
            map_mul' _ _ := Subsingleton.elim _ _
            map_zero' := Subsingleton.elim _ _
            map_add' _ _ := Subsingleton.elim _ _
            commutes' _ := Subsingleton.elim _ _
            map_star' _ := Subsingleton.elim _ _ }
      exact (norm_nonneg _).trans (h PEmpty.{max u v + 1} π₀)
    exact Real.iSup_le (fun ⟨_, ι, π, hp⟩ => hp ▸ h ι π) hc⟩

/-- The universal C⋆-seminorm on `LinearAlgebra.FreeProduct ℂ A`: the supremum of `‖π x‖` over all
unital `⋆`-representations `π` on `lp (fun _ : ι => ℂ) 2` with `ι : Type (max u v)`. -/
def seminorm : CStarSeminorm (LinearAlgebra.FreeProduct ℂ A) where
  __ := seminormAux A
  map_mul_le' x y := seminormAux_le_iff_lp.2 fun ι π => by
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_lp_le_seminormAux π x)
      (norm_lp_le_seminormAux π y) (norm_nonneg _) (apply_nonneg (seminormAux A) x))
  mul_self_le_star_mul_self' x := by
    have hsqrt : seminormAux A x ≤ √(seminormAux A (star x * x)) := by
      refine seminormAux_le_iff_lp.2 fun ι π => ?_
      refine Real.le_sqrt_of_sq_le ?_
      rw [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
      exact norm_lp_le_seminormAux π (star x * x)
    calc seminormAux A x * seminormAux A x
        ≤ √(seminormAux A (star x * x)) * √(seminormAux A (star x * x)) :=
          mul_le_mul hsqrt hsqrt (apply_nonneg _ x) (Real.sqrt_nonneg _)
      _ = seminormAux A (star x * x) := Real.mul_self_sqrt (apply_nonneg _ _)

section SeminormAPI

variable {A}

theorem seminorm_apply (x : LinearAlgebra.FreeProduct ℂ A) :
    seminorm A x =
      sSup {r : ℝ | ∃ (ι : Type (max u v))
        (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ]
          (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)), ‖π x‖ = r} := by
  change seminormAux A x = _
  rw [seminormAux, Seminorm.sSup_apply (bddAbove_representationSeminorms A), iSup]
  congr 1
  ext r
  simp [representationSeminorms]

/-- Every unital Hilbert-space representation of `LinearAlgebra.FreeProduct ℂ A`, on a Hilbert space
in *any* universe `w`, is bounded by `FullFreeProduct.seminorm A`. -/
theorem norm_representation_le_seminorm {H : Type w} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (x : LinearAlgebra.FreeProduct ℂ A) :
    ‖π x‖ ≤ seminorm A x := by
  refine (π x).opNorm_le_bound (apply_nonneg (seminorm A) x) fun ξ => ?_
  obtain ⟨ι, V, hV, η, rfl⟩ :=
    StarAlgHom.exists_linearIsometry_mapsTo_mem_range.{max u v, _, _, _} π ξ
  have hι : ‖π.restrictLinearIsometry hV x‖ ≤ seminorm A x :=
    norm_lp_le_seminormAux (π.restrictLinearIsometry hV) x
  rw [← π.restrictLinearIsometry_apply hV x η, V.norm_map, V.norm_map]
  exact (π.restrictLinearIsometry hV x).le_of_opNorm_le hι η

/-- Every unital `⋆`-homomorphism from `LinearAlgebra.FreeProduct ℂ A` into any unital C⋆-algebra
`B` (in any universe `w`) is bounded by `FullFreeProduct.seminorm A`. -/
theorem norm_starAlgHom_le_seminorm {B : Type w} [CStarAlgebra B]
    (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) (x : LinearAlgebra.FreeProduct ℂ A) :
    ‖ρ x‖ ≤ seminorm A x :=
  TauCeti.CStarAlgebra.norm_le_iff_forall_isNondegenerate.2 fun _ _ _ _ _ hσ => by
    simpa only [StarAlgHom.comp_apply, hσ.toStarAlgHom_apply] using
      norm_representation_le_seminorm (hσ.toStarAlgHom.comp ρ) x

/-- Characterization of `seminorm A x ≤ c` via `ℓ²` representations in universe `max u v`. -/
theorem seminorm_le_iff_lp {x : LinearAlgebra.FreeProduct ℂ A} {c : ℝ} :
    seminorm A x ≤ c ↔
      ∀ (ι : Type (max u v))
        (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ]
          (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)), ‖π x‖ ≤ c :=
  seminormAux_le_iff_lp

/-- Characterization of `seminorm A x ≤ c` via all Hilbert-space representations in universe
`max u v`. -/
theorem seminorm_le_iff_hilbert {x : LinearAlgebra.FreeProduct ℂ A} {c : ℝ} :
    seminorm A x ≤ c ↔
      ∀ (H : Type (max u v)) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)), ‖π x‖ ≤ c :=
  ⟨fun h _ _ _ _ π => (norm_representation_le_seminorm π x).trans h,
    fun h => seminorm_le_iff_lp.2 fun ι π => h (lp (fun _ : ι => ℂ) 2) π⟩

/-- Characterization of `seminorm A x ≤ c` via unital `⋆`-homomorphisms into unital C⋆-algebras in
universe `max u v`. -/
theorem seminorm_le_iff {x : LinearAlgebra.FreeProduct ℂ A} {c : ℝ} :
    seminorm A x ≤ c ↔
      ∀ (B : Type (max u v)) [CStarAlgebra B]
        (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B), ‖ρ x‖ ≤ c :=
  ⟨fun h _ _ ρ => (norm_starAlgHom_le_seminorm ρ x).trans h,
    fun h => seminorm_le_iff_lp.2 fun _ π => h _ π⟩

theorem seminorm_one_le : seminorm A 1 ≤ 1 :=
  seminorm_le_iff_lp.2 fun _ π => by
    rw [map_one, ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le

theorem seminorm_ι_le (i : I) (a : A i) : seminorm A (ι ℂ A i a) ≤ ‖a‖ :=
  seminorm_le_iff_lp.2 fun _ π => by
    rw [← ιStar_apply, ← StarAlgHom.comp_apply]
    exact NonUnitalStarAlgHom.norm_apply_le (π.comp (ιStar ℂ A i)).toNonUnitalStarAlgHom a

/-- When every factor C⋆-algebra `A i` is nontrivial, the universal C⋆-seminorm is isometric on
each canonical factor map `ι ℂ A i₀`. No faithful state on any factor is required: we pair a
norm-attaining state for `star a * a` on `A i₀` with arbitrary states on the remaining factors in
the reduced free-product GNS representation. -/
@[simp]
theorem seminorm_ι [∀ i, Nontrivial (A i)] (i₀ : I) (a : A i₀) :
    seminorm A (ι ℂ A i₀ a) = ‖a‖ := by
  refine le_antisymm (seminorm_ι_le i₀ a) ?_
  choose φ hφ hφb using fun i =>
    TauCeti.CStarAlgebra.exists_starPositiveFunctional_apply_star_mul_self_eq_norm_sq
      (if h : i = i₀ then h ▸ a else (1 : A i))
  let π := ReducedFreeProduct.representation φ hφ
  let Ω := ReducedFreeProduct.vacuum φ hφ
  have hω₀ : φ i₀ (star a * a) = (‖a‖ : ℂ) ^ 2 := by simpa using hφb i₀
  have hsq : ‖π (ι ℂ A i₀ a) Ω‖ ^ 2 = ‖a‖ ^ 2 := by
    rw [π.norm_sq_apply_eq_re_inner_star_mul Ω (ι ℂ A i₀ a), star_ι, ← map_mul (ι ℂ A i₀)]
    have hinner : ⟪Ω, π (ι ℂ A i₀ (star a * a)) Ω⟫_ℂ = φ i₀ (star a * a) := by
      rw [← ReducedFreeProduct.coe_ofAlgebraic φ hφ, ← ReducedFreeProduct.state_apply φ hφ,
        ReducedFreeProduct.state_ofAlgebraic, freeProductPositiveFunctional_ι]
    rw [hinner, hω₀, ← Complex.ofReal_pow]
    exact Complex.ofReal_re (‖a‖ ^ 2)
  have hvec : ‖π (ι ℂ A i₀ a) Ω‖ = ‖a‖ := by
    have h1 := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1
  calc ‖a‖ = ‖π (ι ℂ A i₀ a) Ω‖ := hvec.symm
    _ ≤ ‖π (ι ℂ A i₀ a)‖ * ‖Ω‖ := (π (ι ℂ A i₀ a)).le_opNorm Ω
    _ = ‖π (ι ℂ A i₀ a)‖ := by rw [ReducedFreeProduct.norm_vacuum φ hφ, mul_one]
    _ ≤ seminorm A (ι ℂ A i₀ a) := norm_representation_le_seminorm π (ι ℂ A i₀ a)

@[simp]
theorem seminorm_one [∀ i, Nontrivial (A i)] : seminorm A 1 = 1 := by
  refine le_antisymm seminorm_one_le ?_
  choose φ hφ _ using fun i =>
    TauCeti.CStarAlgebra.exists_starPositiveFunctional_apply_star_mul_self_eq_norm_sq (1 : A i)
  let π := ReducedFreeProduct.representation φ hφ
  let Ω := ReducedFreeProduct.vacuum φ hφ
  calc (1 : ℝ) = ‖Ω‖ := (ReducedFreeProduct.norm_vacuum φ hφ).symm
    _ = ‖π 1 Ω‖ := by rw [map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
    _ ≤ ‖π 1‖ * ‖Ω‖ := (π 1).le_opNorm Ω
    _ = ‖π 1‖ := by rw [ReducedFreeProduct.norm_vacuum φ hφ, mul_one]
    _ ≤ seminorm A 1 := norm_representation_le_seminorm π 1

end SeminormAPI

end FullFreeProduct

/-- The full unital C⋆-free product `*_{i : I} A i` of a family of unital C⋆-algebras `A i`: the
Hausdorff C⋆-completion of `LinearAlgebra.FreeProduct ℂ A` in its universal C⋆-seminorm. -/
@[expose] def FullFreeProduct : Type (max u v) :=
  (FullFreeProduct.seminorm A).Completion

namespace FullFreeProduct

instance : CStarAlgebra (FullFreeProduct A) :=
  inferInstanceAs (CStarAlgebra (seminorm A).Completion)

instance [∀ i, Nontrivial (A i)] : NormOneClass (FullFreeProduct A) :=
  (seminorm A).normOneClass_completion seminorm_one

/-- The canonical unital `⋆`-algebra homomorphism from the algebraic free product into the full
C⋆-free product, with dense range. -/
def ofAlgebraic : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] FullFreeProduct A :=
  (seminorm A).of

section CoreAPI

variable {A}

@[simp]
theorem norm_ofAlgebraic (x : LinearAlgebra.FreeProduct ℂ A) :
    ‖ofAlgebraic A x‖ = seminorm A x :=
  (seminorm A).norm_of x

/-- The image of the algebraic free product is norm dense in `FullFreeProduct A`. -/
theorem denseRange_ofAlgebraic : DenseRange (ofAlgebraic A) :=
  (seminorm A).denseRange_of

/-- Closed properties on `FullFreeProduct A` follow from their restriction to
`LinearAlgebra.FreeProduct ℂ A`. -/
@[elab_as_elim]
theorem induction_on {p : FullFreeProduct A → Prop} (x : FullFreeProduct A)
    (hp : IsClosed {x | p x}) (ih : ∀ a, p (ofAlgebraic A a)) : p x :=
  CStarSeminorm.induction_on x hp ih

/-- The canonical unital `⋆`-homomorphism from the `i`-th factor C⋆-algebra into
`FullFreeProduct A`. -/
def factor (i : I) : A i →⋆ₐ[ℂ] FullFreeProduct A :=
  (ofAlgebraic A).comp (ιStar ℂ A i)

-- Keep `factor` bundled under `simp` so factor-evaluation `@[simp]` lemmas (`lift_factor`,
-- `norm_factor`, `map_factor`, `toReduced_factor`, `state_factor`, etc.) stay in normal form.
theorem factor_apply (i : I) (a : A i) : factor i a = ofAlgebraic A (ι ℂ A i a) := by
  simp [factor]

@[simp]
theorem ofAlgebraic_comp_ιStar (i : I) : (ofAlgebraic A).comp (ιStar ℂ A i) = factor i :=
  (rfl)

@[simp]
theorem factor_toAlgHom (i : I) :
    (factor (A := A) i).toAlgHom = (ofAlgebraic A).toAlgHom.comp (ι ℂ A i) :=
  AlgHom.ext fun a => factor_apply i a

theorem norm_factor_le (i : I) (a : A i) : ‖factor (A := A) i a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le (factor i).toNonUnitalStarAlgHom a

/-- The star-subalgebra images of the factor maps generate `(ofAlgebraic A).range`. -/
theorem iSup_range_factor :
    (⨆ i, (factor (A := A) i).range) = (ofAlgebraic A).range := by
  refine le_antisymm (iSup_le fun i => ?_) ?_
  · rintro _ ⟨a, rfl⟩
    exact ⟨ι ℂ A i a, (factor_apply i a).symm⟩
  · rintro _ ⟨x, rfl⟩
    -- `StarAlgHom.range` unpacks to `(ofAlgebraic A).toAlgHom.toRingHom x`; fold back to `⇑`.
    change ofAlgebraic A x ∈ ⨆ i, (factor (A := A) i).range
    induction x using LinearAlgebra.FreeProduct.induction_on with
    | algebraMap r =>
      rw [AlgHomClass.commutes]
      exact StarSubalgebra.algebraMap_mem _ r
    | ι i a => exact le_iSup (fun j => (factor (A := A) j).range) i ⟨a, factor_apply i a⟩
    | mul x y ihx ihy =>
      rw [map_mul]
      exact mul_mem ihx ihy
    | add x y ihx ihy =>
      rw [map_add]
      exact add_mem ihx ihy

/-- The canonical factor ranges generate `FullFreeProduct A` as a norm-closed star subalgebra. -/
theorem topologicalClosure_iSup_range_factor :
    (⨆ i, (factor (A := A) i).range).topologicalClosure = ⊤ := by
  rw [iSup_range_factor]
  apply SetLike.ext'
  have hcoe : ((ofAlgebraic A).range : Set (FullFreeProduct A)) = Set.range (ofAlgebraic A) :=
    (ofAlgebraic A).toAlgHom.coe_range
  rw [StarSubalgebra.topologicalClosure_coe, hcoe, (denseRange_ofAlgebraic (A := A)).closure_eq]
  rfl

/-- When every factor `A i` is nontrivial, each canonical factor map into `FullFreeProduct A`
preserves norms. -/
@[simp]
theorem norm_factor [∀ i, Nontrivial (A i)] (i : I) (a : A i) :
    ‖factor (A := A) i a‖ = ‖a‖ := by
  rw [factor_apply, norm_ofAlgebraic, seminorm_ι]

/-- When every factor `A i` is nontrivial, each canonical factor map into `FullFreeProduct A` is an
isometry. -/
theorem isometry_factor [∀ i, Nontrivial (A i)] (i : I) :
    Isometry (factor (A := A) i) :=
  AddMonoidHomClass.isometry_of_norm (factor i) (norm_factor i)

/-- When every factor `A i` is nontrivial, each canonical factor map into `FullFreeProduct A` is
injective. -/
theorem factor_injective [∀ i, Nontrivial (A i)] (i : I) :
    Function.Injective (factor (A := A) i) :=
  (isometry_factor i).injective

instance [∀ i, Nontrivial (A i)] : Nontrivial (FullFreeProduct A) :=
  NormOneClass.nontrivial

/-- The full unital C⋆-free product `FullFreeProduct A` is nontrivial if and only if every factor
`A i` is nontrivial (which holds vacuously when `I` is empty). -/
theorem nontrivial_iff : Nontrivial (FullFreeProduct A) ↔ ∀ i, Nontrivial (A i) :=
  ⟨fun _ i => (factor (A := A) i).toRingHom.domain_nontrivial, fun _ => inferInstance⟩

/-- Continuous linear maps out of `FullFreeProduct A` into a Hausdorff space are determined on
`ofAlgebraic A`. -/
@[ext]
theorem continuousLinearMap_ext {E : Type*} [TopologicalSpace E] [T2Space E] [AddCommMonoid E]
    [Module ℂ E] {S T : FullFreeProduct A →L[ℂ] E}
    (h : ∀ a, S (ofAlgebraic A a) = T (ofAlgebraic A a)) : S = T :=
  CStarSeminorm.continuousLinearMap_ext h

/-- Unital `⋆`-homomorphisms from `FullFreeProduct A` into a C⋆-algebra are determined on
`ofAlgebraic A`. -/
theorem starAlgHom_ext_ofAlgebraic {B : Type w} [CStarAlgebra B]
    {Φ Ψ : FullFreeProduct A →⋆ₐ[ℂ] B} (h : Φ.comp (ofAlgebraic A) = Ψ.comp (ofAlgebraic A)) :
    Φ = Ψ :=
  CStarSeminorm.starAlgHom_ext h

/-- Unital `⋆`-homomorphisms from `FullFreeProduct A` into a C⋆-algebra are determined by their
restrictions to the factors `factor i`. -/
@[ext]
theorem starAlgHom_ext {B : Type w} [CStarAlgebra B] {Φ Ψ : FullFreeProduct A →⋆ₐ[ℂ] B}
    (h : ∀ i a, Φ (factor i a) = Ψ (factor i a)) : Φ = Ψ :=
  starAlgHom_ext_ofAlgebraic <| LinearAlgebra.FreeProduct.starAlgHom_ext fun i a => by
    simpa only [StarAlgHom.comp_apply, ← factor_apply] using h i a

/-- `FullFreeProduct A` is the universal unital C⋆-envelope of `LinearAlgebra.FreeProduct ℂ A`:
unital `⋆`-homomorphisms out of `LinearAlgebra.FreeProduct ℂ A` into any unital C⋆-algebra `B`
(in any universe `w`) correspond bijectively to unital `⋆`-homomorphisms out of
`FullFreeProduct A`. -/
def liftAlgebraic {B : Type w} [CStarAlgebra B] :
    (LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) ≃ (FullFreeProduct A →⋆ₐ[ℂ] B) where
  toFun ρ := (seminorm A).lift ρ (norm_starAlgHom_le_seminorm ρ)
  invFun Φ := Φ.comp (ofAlgebraic A)
  left_inv ρ := (seminorm A).lift_comp_of ρ (norm_starAlgHom_le_seminorm ρ)
  right_inv Φ := starAlgHom_ext_ofAlgebraic
    ((seminorm A).lift_comp_of (Φ.comp (ofAlgebraic A)) _)

@[simp]
theorem liftAlgebraic_ofAlgebraic {B : Type w} [CStarAlgebra B]
    (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) (a : LinearAlgebra.FreeProduct ℂ A) :
    liftAlgebraic ρ (ofAlgebraic A a) = ρ a :=
  (seminorm A).lift_of ρ (norm_starAlgHom_le_seminorm ρ) a

@[simp]
theorem liftAlgebraic_comp_ofAlgebraic {B : Type w} [CStarAlgebra B]
    (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) :
    (liftAlgebraic ρ).comp (ofAlgebraic A) = ρ :=
  liftAlgebraic.symm_apply_apply ρ

@[simp]
theorem liftAlgebraic_symm_apply {B : Type w} [CStarAlgebra B] (Φ : FullFreeProduct A →⋆ₐ[ℂ] B) :
    liftAlgebraic.symm Φ = Φ.comp (ofAlgebraic A) :=
  (rfl)

/-- Extend a unital Hilbert-space representation of `LinearAlgebra.FreeProduct ℂ A` (in any
universe `w`) by continuity to a unital `⋆`-representation of `FullFreeProduct A`. -/
def liftRepresentation {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    FullFreeProduct A →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  liftAlgebraic (B := H →L[ℂ] H) π

@[simp]
theorem liftRepresentation_ofAlgebraic {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (x : LinearAlgebra.FreeProduct ℂ A) :
    liftRepresentation π (ofAlgebraic A x) = π x :=
  liftAlgebraic_ofAlgebraic (B := H →L[ℂ] H) π x

@[simp]
theorem liftRepresentation_factor {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) (i : I) (a : A i) :
    liftRepresentation π (factor i a) = π (ι ℂ A i a) := by
  rw [factor_apply, liftRepresentation_ofAlgebraic]

open scoped _root_.CStarAlgebra in
/-- The range of `liftRepresentation π` is the norm closure of the algebraic image `π.range`. -/
theorem range_liftRepresentation {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (liftRepresentation π).range = π.range.topologicalClosure := by
  apply SetLike.ext'
  have hcoeL : ((liftRepresentation π).range : Set (H →L[ℂ] H)) =
      Set.range (liftRepresentation π) :=
    (liftRepresentation π).toAlgHom.coe_range
  have hcoe : (π.range : Set (H →L[ℂ] H)) = Set.range π := π.toAlgHom.coe_range
  rw [hcoeL, StarSubalgebra.topologicalClosure_coe, hcoe]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    refine induction_on x (isClosed_closure.preimage (map_continuous (liftRepresentation π)))
      fun a => ?_
    rw [liftRepresentation_ofAlgebraic]
    exact subset_closure ⟨a, rfl⟩
  · refine (liftRepresentation π).isClosed_setRange.closure_subset_iff.mpr ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨ofAlgebraic A a, liftRepresentation_ofAlgebraic π a⟩

/-- Membership in `(liftRepresentation π).range` is membership in the norm closure of
`Set.range π`. -/
theorem mem_range_liftRepresentation_iff {H : Type w} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    T ∈ (liftRepresentation π).range ↔ T ∈ closure (Set.range π) := by
  have hcoe : (π.range : Set (H →L[ℂ] H)) = Set.range π := π.toAlgHom.coe_range
  rw [range_liftRepresentation, ← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe, hcoe]

/-- Universal coproduct property of the full unital C⋆-free product: families of unital
`⋆`-homomorphisms `f : (i : I) → A i →⋆ₐ[ℂ] B` into any unital C⋆-algebra `B` (in any universe `w`)
correspond bijectively to unital `⋆`-homomorphisms `FullFreeProduct A →⋆ₐ[ℂ] B`. -/
def lift {B : Type w} [CStarAlgebra B] :
    ((i : I) → A i →⋆ₐ[ℂ] B) ≃ (FullFreeProduct A →⋆ₐ[ℂ] B) :=
  ({ toFun := fun f {i} => f i
     invFun := fun f i => f (i := i)
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } :
    ((i : I) → A i →⋆ₐ[ℂ] B) ≃ ({i : I} → A i →⋆ₐ[ℂ] B)).trans
    (liftStar.trans liftAlgebraic)

theorem lift_eq_liftAlgebraic {B : Type w} [CStarAlgebra B] (f : (i : I) → A i →⋆ₐ[ℂ] B) :
    lift f = liftAlgebraic (liftStar fun {i} => f i) :=
  (rfl)

@[simp]
theorem lift_ofAlgebraic {B : Type w} [CStarAlgebra B] (f : (i : I) → A i →⋆ₐ[ℂ] B)
    (x : LinearAlgebra.FreeProduct ℂ A) :
    lift f (ofAlgebraic A x) = liftStar (fun {i} => f i) x :=
  liftAlgebraic_ofAlgebraic _ x

@[simp]
theorem lift_factor {B : Type w} [CStarAlgebra B] (f : (i : I) → A i →⋆ₐ[ℂ] B) (i : I) (a : A i) :
    lift f (factor i a) = f i a := by
  rw [factor_apply, lift_ofAlgebraic, liftStar_ι]

@[simp]
theorem lift_comp_factor {B : Type w} [CStarAlgebra B] (f : (i : I) → A i →⋆ₐ[ℂ] B) (i : I) :
    (lift f).comp (factor i) = f i :=
  StarAlgHom.ext (lift_factor f i)

@[simp]
theorem lift_symm_apply {B : Type w} [CStarAlgebra B] (Φ : FullFreeProduct A →⋆ₐ[ℂ] B) (i : I) :
    lift.symm Φ i = Φ.comp (factor i) := by
  ext a
  simp [lift, factor_apply]

@[simp]
theorem lift_factor_eq_id :
    lift (factor (A := A)) = StarAlgHom.id ℂ (FullFreeProduct A) := by
  ext i a
  simp

@[simp]
theorem lift_comp {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]
    (f : (i : I) → A i →⋆ₐ[ℂ] B) (g : B →⋆ₐ[ℂ] C) :
    lift (fun i => g.comp (f i)) = g.comp (lift f) := by
  ext i a
  simp

theorem norm_lift_le {B : Type w} [CStarAlgebra B] (f : (i : I) → A i →⋆ₐ[ℂ] B)
    (x : FullFreeProduct A) : ‖lift f x‖ ≤ ‖x‖ :=
  NonUnitalStarAlgHom.norm_apply_le (lift f).toNonUnitalStarAlgHom x

/-- The norm of `x : FullFreeProduct A` is the least upper bound of `‖liftAlgebraic π x‖` over all
`ℓ²` representations `π` in universe `max u v`. -/
theorem norm_le_iff_lp {x : FullFreeProduct A} {c : ℝ} :
    ‖x‖ ≤ c ↔
      ∀ (ι : Type (max u v))
        (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ]
          (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)),
        ‖liftAlgebraic π x‖ ≤ c := by
  refine ⟨fun h ι π => (NonUnitalStarAlgHom.norm_apply_le _ x).trans h, fun h => ?_⟩
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨a, ha⟩ := (denseRange_ofAlgebraic (A := A)).exists_dist_lt x (half_pos hε)
  have ha' : ‖x - ofAlgebraic A a‖ < ε / 2 := by rwa [← dist_eq_norm]
  have hac : ‖ofAlgebraic A a‖ ≤ c + ε / 2 := by
    rw [norm_ofAlgebraic, seminorm_le_iff_lp]
    intro ι π
    rw [← liftAlgebraic_ofAlgebraic π a]
    calc ‖liftAlgebraic π (ofAlgebraic A a)‖
        ≤ ‖liftAlgebraic π x‖ + ‖liftAlgebraic π (x - ofAlgebraic A a)‖ := by
          rw [map_sub, norm_sub_rev]
          exact norm_le_insert' _ _
      _ ≤ c + ε / 2 :=
          add_le_add (h ι π) ((NonUnitalStarAlgHom.norm_apply_le _ _).trans ha'.le)
  calc ‖x‖ ≤ ‖ofAlgebraic A a‖ + ‖x - ofAlgebraic A a‖ := norm_le_insert' x (ofAlgebraic A a)
    _ < c + ε := by linarith

/-- Two algebraic free-product elements map to the same element of `FullFreeProduct A` if and only
if they agree in every `ℓ²` representation in universe `max u v`. -/
theorem ofAlgebraic_eq_iff {a b : LinearAlgebra.FreeProduct ℂ A} :
    ofAlgebraic A a = ofAlgebraic A b ↔
      ∀ (ι : Type (max u v))
        (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ]
          (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)), π a = π b := by
  refine ⟨fun h ι π => by simpa using congr(liftAlgebraic π $h), fun h => ?_⟩
  rw [← sub_eq_zero, ← map_sub, ← norm_eq_zero, norm_ofAlgebraic]
  refine le_antisymm (seminorm_le_iff_lp.2 fun ι π => ?_) (apply_nonneg _ _)
  rw [map_sub, h ι π, sub_self, norm_zero]

/-- Any unital `⋆`-algebra equivalence between algebraic free products of unital C⋆-algebras lifts
canonically to an isometric `⋆`-isomorphism between their full unital C⋆-free products. -/
def congrAlgebraic {J : Type*} [DecidableEq J] {B : J → Type*} [∀ j, CStarAlgebra (B j)]
    (e : LinearAlgebra.FreeProduct ℂ A ≃⋆ₐ[ℂ] LinearAlgebra.FreeProduct ℂ B) :
    FullFreeProduct A ≃⋆ₐ[ℂ] FullFreeProduct B :=
  StarAlgEquiv.ofStarAlgHom
    (liftAlgebraic ((ofAlgebraic B).comp e.toStarAlgHom))
    (liftAlgebraic ((ofAlgebraic A).comp e.symm.toStarAlgHom))
    (starAlgHom_ext_ofAlgebraic <| StarAlgHom.ext fun x => by simp)
    (starAlgHom_ext_ofAlgebraic <| StarAlgHom.ext fun y => by simp)

@[simp]
theorem congrAlgebraic_ofAlgebraic {J : Type*} [DecidableEq J] {B : J → Type*}
    [∀ j, CStarAlgebra (B j)]
    (e : LinearAlgebra.FreeProduct ℂ A ≃⋆ₐ[ℂ] LinearAlgebra.FreeProduct ℂ B)
    (x : LinearAlgebra.FreeProduct ℂ A) :
    congrAlgebraic e (ofAlgebraic A x) = ofAlgebraic B (e x) := by
  simp [congrAlgebraic]

@[simp]
theorem congrAlgebraic_symm {J : Type*} [DecidableEq J] {B : J → Type*} [∀ j, CStarAlgebra (B j)]
    (e : LinearAlgebra.FreeProduct ℂ A ≃⋆ₐ[ℂ] LinearAlgebra.FreeProduct ℂ B) :
    (congrAlgebraic e).symm = congrAlgebraic e.symm :=
  (rfl)

end CoreAPI

section EmptyAndCombinators

/-- The full unital C⋆-free product over an empty index type is canonically (and hence
isometrically) `⋆`-isomorphic to `ℂ`. -/
def isEmptyEquiv [IsEmpty I] : FullFreeProduct A ≃⋆ₐ[ℂ] ℂ :=
  StarAlgEquiv.ofStarAlgHom
    (lift fun i => isEmptyElim i)
    (StarAlgHom.ofId ℂ (FullFreeProduct A))
    (starAlgHom_ext fun i => isEmptyElim i)
    (StarAlgHom.ext fun c => AlgHomClass.commutes (lift (A := A) fun i => isEmptyElim i) c)

@[simp]
theorem isEmptyEquiv_ofAlgebraic [IsEmpty I] (x : LinearAlgebra.FreeProduct ℂ A) :
    isEmptyEquiv A (ofAlgebraic A x) = isEmptyStarAlgEquiv ℂ A x :=
  DFunLike.congr_fun
    (LinearAlgebra.FreeProduct.starAlgHom_ext
      (f := (isEmptyEquiv A).toStarAlgHom.comp (ofAlgebraic A))
      (g := (isEmptyStarAlgEquiv ℂ A).toStarAlgHom) fun i => isEmptyElim i) x

@[simp]
theorem isEmptyEquiv_symm_apply [IsEmpty I] (c : ℂ) :
    (isEmptyEquiv A).symm c = algebraMap ℂ (FullFreeProduct A) c :=
  (rfl)

section Functoriality

variable {A}

/-- Functoriality of `FullFreeProduct`: a family of unital `⋆`-homomorphisms `f i : A i →⋆ₐ[ℂ] A' i`
induces a unital `⋆`-homomorphism `FullFreeProduct A →⋆ₐ[ℂ] FullFreeProduct A'`. -/
def map {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (f : (i : I) → A i →⋆ₐ[ℂ] A' i) : FullFreeProduct A →⋆ₐ[ℂ] FullFreeProduct A' :=
  lift fun i => (factor (A := A') i).comp (f i)

@[simp]
theorem map_factor {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (f : (i : I) → A i →⋆ₐ[ℂ] A' i) (i : I) (a : A i) :
    map f (factor i a) = factor i (f i a) := by
  rw [map, lift_factor, StarAlgHom.comp_apply]

@[simp]
theorem map_comp_factor {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (f : (i : I) → A i →⋆ₐ[ℂ] A' i) (i : I) :
    (map f).comp (factor i) = (factor i).comp (f i) := by
  rw [map, lift_comp_factor]

@[simp]
theorem map_ofAlgebraic {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (f : (i : I) → A i →⋆ₐ[ℂ] A' i) (x : LinearAlgebra.FreeProduct ℂ A) :
    map f (ofAlgebraic A x) = ofAlgebraic A' (mapStar f x) := by
  have h : (map f).comp (ofAlgebraic A) = (ofAlgebraic A').comp (mapStar f) := by
    ext i a
    simp [← factor_apply]
  exact DFunLike.congr_fun h x

@[simp]
theorem map_id :
    map (fun i => StarAlgHom.id ℂ (A i)) = StarAlgHom.id ℂ (FullFreeProduct A) := by
  ext i a
  simp

theorem map_comp {A' A'' : I → Type*} [∀ i, CStarAlgebra (A' i)] [∀ i, CStarAlgebra (A'' i)]
    (g : (i : I) → A' i →⋆ₐ[ℂ] A'' i) (f : (i : I) → A i →⋆ₐ[ℂ] A' i) :
    map (fun i => (g i).comp (f i)) = (map g).comp (map f) := by
  ext i a
  simp

/-- If every factor `⋆`-homomorphism `f i` is surjective, then `FullFreeProduct.map f` is
surjective. -/
theorem map_surjective {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    {f : (i : I) → A i →⋆ₐ[ℂ] A' i} (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (map f) := by
  refine StarAlgHom.surjective_of_denseRange ?_
  refine (denseRange_ofAlgebraic (A := A')).mono ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := mapStar_surjective hf y
  exact ⟨ofAlgebraic A x, map_ofAlgebraic f x⟩

/-- Factorwise `⋆`-isomorphisms induce an isometric `⋆`-isomorphism of full C⋆-free products. -/
def mapEquiv {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (e : (i : I) → A i ≃⋆ₐ[ℂ] A' i) : FullFreeProduct A ≃⋆ₐ[ℂ] FullFreeProduct A' :=
  congrAlgebraic (mapStarEquiv e)

@[simp]
theorem mapEquiv_ofAlgebraic {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (e : (i : I) → A i ≃⋆ₐ[ℂ] A' i) (x : LinearAlgebra.FreeProduct ℂ A) :
    mapEquiv e (ofAlgebraic A x) = ofAlgebraic A' (mapStarEquiv e x) :=
  congrAlgebraic_ofAlgebraic (mapStarEquiv e) x

@[simp]
theorem mapEquiv_toStarAlgHom {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (e : (i : I) → A i ≃⋆ₐ[ℂ] A' i) :
    (mapEquiv e).toStarAlgHom = map fun i => (e i).toStarAlgHom := by
  ext i a
  simp [mapEquiv, factor_apply]

@[simp]
theorem mapEquiv_factor {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (e : (i : I) → A i ≃⋆ₐ[ℂ] A' i) (i : I) (a : A i) :
    mapEquiv e (factor i a) = factor i (e i a) := by
  simp [factor_apply]

@[simp]
theorem mapEquiv_symm {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (e : (i : I) → A i ≃⋆ₐ[ℂ] A' i) :
    (mapEquiv e).symm = mapEquiv fun i => (e i).symm := by
  rw [mapEquiv, congrAlgebraic_symm, mapStarEquiv_symm, ← mapEquiv]

end Functoriality

/-- Pull back the index set of a full C⋆-free product along any map `f : J → I`. -/
def reindexHom {J : Type*} [DecidableEq J] (f : J → I) :
    FullFreeProduct (fun j => A (f j)) →⋆ₐ[ℂ] FullFreeProduct A :=
  lift fun j => factor (A := A) (f j)

@[simp]
theorem reindexHom_factor {J : Type*} [DecidableEq J] (f : J → I) (j : J) (a : A (f j)) :
    reindexHom A f (factor (A := fun k => A (f k)) j a) = factor (A := A) (f j) a := by
  rw [reindexHom, lift_factor]

@[simp]
theorem reindexHom_ofAlgebraic {J : Type*} [DecidableEq J] (f : J → I)
    (x : LinearAlgebra.FreeProduct ℂ fun j => A (f j)) :
    reindexHom A f (ofAlgebraic (fun j => A (f j)) x) =
      ofAlgebraic A (reindexStarHom ℂ A f x) := by
  have h : (reindexHom A f).comp (ofAlgebraic (fun j => A (f j))) =
      (ofAlgebraic A).comp (reindexStarHom ℂ A f) := by
    ext j a
    simp [← factor_apply]
  exact DFunLike.congr_fun h x

/-- Relabeling the index type along an equivalence `σ : J ≃ I` induces an isometric `⋆`-isomorphism
of full C⋆-free products. -/
def reindexEquiv {J : Type*} [DecidableEq J] (σ : J ≃ I) :
    FullFreeProduct (fun j => A (σ j)) ≃⋆ₐ[ℂ] FullFreeProduct A :=
  congrAlgebraic (reindexStarAlgEquiv ℂ A σ)

@[simp]
theorem reindexEquiv_ofAlgebraic {J : Type*} [DecidableEq J] (σ : J ≃ I)
    (x : LinearAlgebra.FreeProduct ℂ fun j => A (σ j)) :
    reindexEquiv A σ (ofAlgebraic (fun j => A (σ j)) x) =
      ofAlgebraic A (reindexStarAlgEquiv ℂ A σ x) :=
  congrAlgebraic_ofAlgebraic (reindexStarAlgEquiv ℂ A σ) x

@[simp]
theorem reindexEquiv_toStarAlgHom {J : Type*} [DecidableEq J] (σ : J ≃ I) :
    (reindexEquiv A σ).toStarAlgHom = reindexHom A σ := by
  ext j a
  simp [reindexEquiv, factor_apply]

@[simp]
theorem reindexEquiv_factor {J : Type*} [DecidableEq J] (σ : J ≃ I) (j : J) (a : A (σ j)) :
    reindexEquiv A σ (factor (A := fun k => A (σ k)) j a) = factor (A := A) (σ j) a := by
  simp [factor_apply]

@[simp]
theorem reindexEquiv_symm_factor {J : Type*} [DecidableEq J] (σ : J ≃ I) (j : J) (a : A (σ j)) :
    (reindexEquiv A σ).symm (factor (A := A) (σ j) a) =
      factor (A := fun k => A (σ k)) j a :=
  (reindexEquiv A σ).symm_apply_eq.mpr (reindexEquiv_factor A σ j a).symm

/-- Associativity (sigma grouping) for the full unital C⋆-free product: the full C⋆-free product
indexed by `Σ j, κ j` is canonically (and hence isometrically) `⋆`-isomorphic to the iterated full
C⋆-free product over `j` and `κ j`. -/
def sigmaEquiv {J : Type*} [DecidableEq J] {κ : J → Type*} [∀ j, DecidableEq (κ j)]
    (B : (j : J) → κ j → Type*) [∀ j k, CStarAlgebra (B j k)] :
    FullFreeProduct (fun p : Σ j, κ j => B p.1 p.2) ≃⋆ₐ[ℂ]
      FullFreeProduct (fun j => FullFreeProduct (B j)) :=
  StarAlgEquiv.ofStarAlgHom
    (lift fun p => (factor (A := fun j => FullFreeProduct (B j)) p.1).comp
      (factor (A := B p.1) p.2))
    (lift fun j => lift fun k => factor (A := fun p : Σ j, κ j => B p.1 p.2) ⟨j, k⟩)
    (starAlgHom_ext fun p b => by
      rcases p with ⟨j, k⟩
      simp)
    (starAlgHom_ext fun j x => by
      have hj :
          ((lift fun p : Σ j, κ j =>
              (factor (A := fun j => FullFreeProduct (B j)) p.1).comp
                (factor (A := B p.1) p.2)).comp
            (lift fun k => factor (A := fun p : Σ j, κ j => B p.1 p.2) ⟨j, k⟩)) =
            factor (A := fun j => FullFreeProduct (B j)) j :=
        starAlgHom_ext fun k b => by simp
      simpa using DFunLike.congr_fun hj x)

@[simp]
theorem sigmaEquiv_factor {J : Type*} [DecidableEq J] {κ : J → Type*} [∀ j, DecidableEq (κ j)]
    (B : (j : J) → κ j → Type*) [∀ j k, CStarAlgebra (B j k)] (j : J) (k : κ j) (b : B j k) :
    sigmaEquiv B (factor (A := fun p : Σ j, κ j => B p.1 p.2) ⟨j, k⟩ b) =
      factor (A := fun j => FullFreeProduct (B j)) j (factor (A := B j) k b) := by
  simp [sigmaEquiv]

@[simp]
theorem sigmaEquiv_symm_factor {J : Type*} [DecidableEq J] {κ : J → Type*}
    [∀ j, DecidableEq (κ j)] (B : (j : J) → κ j → Type*) [∀ j k, CStarAlgebra (B j k)]
    (j : J) (k : κ j) (b : B j k) :
    (sigmaEquiv B).symm
      (factor (A := fun j => FullFreeProduct (B j)) j (factor (A := B j) k b)) =
      factor (A := fun p : Σ j, κ j => B p.1 p.2) ⟨j, k⟩ b :=
  (sigmaEquiv B).symm_apply_eq.mpr (sigmaEquiv_factor B j k b).symm

/-- Grouping the factors of `FullFreeProduct A` along any indexing map `p : I → J` identifies
`FullFreeProduct A` with the full C⋆-free product over `j : J` of the fiber full C⋆-free products
over `{i : I // p i = j}`. -/
def fiberEquiv {J : Type*} [DecidableEq J] (p : I → J) :
    FullFreeProduct A ≃⋆ₐ[ℂ]
      FullFreeProduct (fun j : J => FullFreeProduct (fun i : {i : I // p i = j} => A i.1)) :=
  (reindexEquiv A (Equiv.sigmaFiberEquiv p)).symm.trans
    (sigmaEquiv fun j (i : {i : I // p i = j}) => A i.1)

@[simp]
theorem fiberEquiv_factor {J : Type*} [DecidableEq J] (p : I → J) (i : I) (a : A i) :
    fiberEquiv A p (factor (A := A) i a) =
      factor (A := fun j : J => FullFreeProduct (fun k : {k : I // p k = j} => A k.1)) (p i)
        (factor (A := fun k : {k : I // p k = p i} => A k.1) ⟨i, rfl⟩ a) := by
  have h1 : (reindexEquiv A (Equiv.sigmaFiberEquiv p)).symm (factor (A := A) i a) =
      factor (A := fun q : Σ j : J, {k : I // p k = j} => A (Equiv.sigmaFiberEquiv p q))
        ⟨p i, ⟨i, rfl⟩⟩ a :=
    reindexEquiv_symm_factor A (Equiv.sigmaFiberEquiv p) ⟨p i, ⟨i, rfl⟩⟩ a
  exact (congrArg (sigmaEquiv fun j (k : {k : I // p k = j}) => A k.1) h1).trans
    (sigmaEquiv_factor (fun j (k : {k : I // p k = j}) => A k.1) (p i) ⟨i, rfl⟩ a)

@[simp]
theorem fiberEquiv_symm_factor {J : Type*} [DecidableEq J] (p : I → J)
    (j : J) (i : {i : I // p i = j}) (a : A i.1) :
    (fiberEquiv A p).symm
      (factor (A := fun j' : J => FullFreeProduct (fun k : {k : I // p k = j'} => A k.1)) j
        (factor (A := fun k : {k : I // p k = j} => A k.1) i a)) = factor (A := A) i.1 a := by
  obtain ⟨i, rfl⟩ := i
  exact (fiberEquiv A p).symm_apply_eq.mpr (fiberEquiv_factor A p i a).symm

end EmptyAndCombinators

section ReducedQuotientAndState

variable {A}
variable (φ : ∀ i, StarPositiveFunctional (A i)) (hφ : ∀ i, φ i 1 = 1)

/-- The reduced GNS representation of `LinearAlgebra.FreeProduct ℂ A` associated to normalized
factor functionals `φ`, extended by continuity to `FullFreeProduct A`. -/
def reducedRepresentation :
    FullFreeProduct A →⋆ₐ[ℂ]
      (ReducedFreeProduct.HilbertSpace φ hφ →L[ℂ] ReducedFreeProduct.HilbertSpace φ hφ) :=
  liftRepresentation (ReducedFreeProduct.representation φ hφ)

@[simp]
theorem reducedRepresentation_ofAlgebraic (x : LinearAlgebra.FreeProduct ℂ A) :
    reducedRepresentation φ hφ (ofAlgebraic A x) = ReducedFreeProduct.representation φ hφ x :=
  liftRepresentation_ofAlgebraic (ReducedFreeProduct.representation φ hφ) x

/-- The range of `reducedRepresentation φ hφ` is the reduced C⋆-free product
`ReducedFreeProduct.algebra φ hφ`. -/
theorem range_reducedRepresentation :
    (reducedRepresentation φ hφ).range = ReducedFreeProduct.algebra φ hφ := by
  ext T
  rw [reducedRepresentation, mem_range_liftRepresentation_iff, ReducedFreeProduct.mem_algebra_iff]

/-- The canonical unital `⋆`-homomorphism from `FullFreeProduct A` onto the reduced C⋆-free product
`ReducedFreeProduct.algebra φ hφ` associated to normalized factor functionals `φ`. -/
def toReduced : FullFreeProduct A →⋆ₐ[ℂ] ReducedFreeProduct.algebra φ hφ :=
  (reducedRepresentation φ hφ).codRestrict (ReducedFreeProduct.algebra φ hφ) fun x => by
    rw [← range_reducedRepresentation]
    exact ⟨x, rfl⟩

@[simp]
theorem coe_toReduced (x : FullFreeProduct A) :
    (toReduced φ hφ x :
      ReducedFreeProduct.HilbertSpace φ hφ →L[ℂ] ReducedFreeProduct.HilbertSpace φ hφ) =
      reducedRepresentation φ hφ x :=
  (rfl)

@[simp]
theorem toReduced_ofAlgebraic (x : LinearAlgebra.FreeProduct ℂ A) :
    toReduced φ hφ (ofAlgebraic A x) = ReducedFreeProduct.ofAlgebraic φ hφ x := by
  ext
  simp [ReducedFreeProduct.coe_ofAlgebraic]

@[simp]
theorem toReduced_factor (i : I) (a : A i) :
    toReduced φ hφ (factor i a) = ReducedFreeProduct.factor φ hφ i a := by
  simp [factor_apply, ReducedFreeProduct.factor_apply]

/-- The canonical `⋆`-homomorphism `toReduced φ hφ` onto `ReducedFreeProduct.algebra φ hφ` is
surjective: every reduced C⋆-free product is a C⋆-quotient of the full C⋆-free product. -/
theorem toReduced_surjective : Function.Surjective (toReduced φ hφ) := by
  rintro ⟨T, hT⟩
  rw [← range_reducedRepresentation] at hT
  obtain ⟨x, hx⟩ := hT
  exact ⟨x, Subtype.ext hx⟩

theorem ker_toReduced :
    TwoSidedIdeal.ker (toReduced φ hφ) = TwoSidedIdeal.ker (reducedRepresentation φ hφ) :=
  SetLike.ext fun _ => (TwoSidedIdeal.mem_ker (toReduced φ hφ)).trans <|
    Subtype.ext_iff.trans (TwoSidedIdeal.mem_ker (reducedRepresentation φ hφ)).symm

/-- First `⋆`-isomorphism theorem identifying `ReducedFreeProduct.algebra φ hφ` with the
C⋆-quotient of `FullFreeProduct A` by `TwoSidedIdeal.ker (toReduced φ hφ)`. -/
def quotientKerToReducedEquiv :
    FullFreeProduct A ⧸ TwoSidedIdeal.ker (toReduced φ hφ) ≃⋆ₐ[ℂ]
      ReducedFreeProduct.algebra φ hφ :=
  StarAlgHom.quotientKerEquivOfSurjective (toReduced_surjective φ hφ)

theorem quotientKerToReducedEquiv_mk (x : FullFreeProduct A) :
    quotientKerToReducedEquiv φ hφ
      (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker (toReduced φ hφ)) x) = toReduced φ hφ x :=
  StarAlgHom.quotientKerEquivOfSurjective_mk (toReduced_surjective φ hφ) x

/-- The vacuum positive functional on `FullFreeProduct A` pulled back along
`reducedRepresentation φ hφ`, agreeing with `ReducedFreeProduct.state φ hφ` along
`toReduced φ hφ`. -/
def state : StarPositiveFunctional (FullFreeProduct A) :=
  (StarPositiveFunctional.ofPositiveLinearMap
    (ContinuousLinearMap.innerPositiveLinearMap ℂ (ReducedFreeProduct.vacuum φ hφ))).comp
    (reducedRepresentation φ hφ)

theorem state_apply_eq_reduced (x : FullFreeProduct A) :
    state φ hφ x = ReducedFreeProduct.state φ hφ (toReduced φ hφ x) := by
  simp [state, ReducedFreeProduct.state_apply]

@[simp]
theorem state_ofAlgebraic (x : LinearAlgebra.FreeProduct ℂ A) :
    state φ hφ (ofAlgebraic A x) = freeProductPositiveFunctional φ hφ x := by
  simp [state_apply_eq_reduced]

@[simp]
theorem state_one : state φ hφ 1 = 1 := by
  rw [← map_one (ofAlgebraic A), state_ofAlgebraic, freeProductPositiveFunctional_one]

@[simp]
theorem state_factor (i : I) (a : A i) : state φ hφ (factor i a) = φ i a := by
  simp [factor_apply]

/-- The canonical factor subalgebras `(factor i).toAlgHom.range` in `FullFreeProduct A` are freely
independent with respect to `FullFreeProduct.state φ hφ`. -/
theorem isFreelyIndependent_factor :
    IsFreelyIndependent (state φ hφ).toLinearMap
      (fun i => (factor (A := A) i).toAlgHom.range) := by
  have h := (isFreelyIndependent_freeProductExpectation
    (fun i => (φ i).toLinearMap) hφ).map (ofAlgebraic A).toAlgHom
    (φ' := (state φ hφ).toLinearMap)
    (by
      ext x
      simp [freeProductPositiveFunctional_apply])
  have hranges : (fun i => (factor (A := A) i).toAlgHom.range) =
      (fun i => ((ι ℂ A i).range).map (ofAlgebraic A).toAlgHom) := by
    funext i
    rw [factor_toAlgHom, AlgHom.range_comp]
  rwa [← hranges] at h

end ReducedQuotientAndState

end FullFreeProduct

end SeminormAndCompletion

end TauCeti
