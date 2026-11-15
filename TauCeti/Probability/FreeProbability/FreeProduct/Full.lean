/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Topology.Algebra.LinearMapCompletion
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

Equipping the type synonym `FullAlgebraicFreeProduct A` with this C⋆-seminorm and taking its
Hausdorff uniform completion yields the *full unital C⋆-free product* `FullFreeProduct A`, a unital
C⋆-algebra in universe `max u v`. It satisfies the coproduct universal property
`FullFreeProduct.lift : ((i : I) → A i →⋆ₐ[ℂ] B) ≃ (FullFreeProduct A →⋆ₐ[ℂ] B)` for any unital
C⋆-algebra `B` in any universe `w`.

When every factor `A i` is nontrivial, no faithful state on any `A i` is required to embed the
factors isometrically: for a given `a : A i₀`, choosing a norm-attaining state on `star a * a` at
`i₀` and arbitrary states on the remaining factors in `ReducedFreeProduct.representation` shows
`FullFreeProduct.seminorm A (ι ℂ A i₀ a) = ‖a‖`, so `FullFreeProduct.factor i₀` is isometric and
injective (`FullFreeProduct.isometry_factor`, `FullFreeProduct.factor_injective`), and
`Nontrivial (FullFreeProduct A) ↔ ∀ i, Nontrivial (A i)` (`FullFreeProduct.nontrivial_iff`).

The empty full C⋆-free product is canonically `⋆`-isomorphic to `ℂ`
(`FullFreeProduct.isEmptyEquiv`). Factorwise `⋆`-homomorphisms, index relabelings, sigma
associativity, and fiber grouping lift to `FullFreeProduct.map`, `FullFreeProduct.mapEquiv`,
`FullFreeProduct.reindexEquiv`, `FullFreeProduct.sigmaEquiv`, and `FullFreeProduct.fiberEquiv`.
Given normalized positive functionals `φ i` on the factors, `FullFreeProduct.toReduced φ hφ` is a
surjective unital `⋆`-homomorphism onto `ReducedFreeProduct.algebra φ hφ`, exhibiting the reduced
C⋆-free product as a quotient of `FullFreeProduct A` (`FullFreeProduct.quotientKerToReducedEquiv`)
and pulling the vacuum state and freeness of the factors back to `FullFreeProduct A`.

## Main definitions

* `TauCeti.FullFreeProduct.seminorm`: the universal C⋆-seminorm on
  `LinearAlgebra.FreeProduct ℂ A`.
* `TauCeti.FullAlgebraicFreeProduct`: type synonym of `LinearAlgebra.FreeProduct ℂ A` carrying the
  universal C⋆-seminorm.
* `TauCeti.FullFreeProduct`: the full unital C⋆-free product of `A`, a unital C⋆-algebra.
* `TauCeti.FullFreeProduct.ofAlgebraic` and `TauCeti.FullFreeProduct.factor`: the canonical dense
  unital `⋆`-homomorphism from `LinearAlgebra.FreeProduct ℂ A` and the canonical factor maps.
* `TauCeti.FullFreeProduct.liftAlgebraic`, `TauCeti.FullFreeProduct.liftRepresentation`, and
  `TauCeti.FullFreeProduct.lift`: universal properties with respect to unital C⋆-algebras and
  Hilbert-space representations in any universe.
* `TauCeti.FullFreeProduct.isEmptyEquiv`, `TauCeti.FullFreeProduct.map`,
  `TauCeti.FullFreeProduct.mapEquiv`, `TauCeti.FullFreeProduct.reindexEquiv`,
  `TauCeti.FullFreeProduct.sigmaEquiv`, and `TauCeti.FullFreeProduct.fiberEquiv`: empty product,
  functoriality, relabeling, and associativity/grouping.
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

open LinearAlgebra.FreeProduct UniformSpace
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

/-- The universal C⋆-seminorm on `LinearAlgebra.FreeProduct ℂ A`: the supremum of `‖π x‖` over all
unital `⋆`-representations `π` on `lp (fun _ : ι => ℂ) 2` with `ι : Type (max u v)`. -/
def seminorm : Seminorm ℂ (LinearAlgebra.FreeProduct ℂ A) :=
  sSup (representationSeminorms A)

section SeminormAPI

variable {A}

theorem seminorm_apply (x : LinearAlgebra.FreeProduct ℂ A) :
    seminorm A x =
      sSup {r : ℝ | ∃ (ι : Type (max u v))
        (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ]
          (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)), ‖π x‖ = r} := by
  rw [seminorm, Seminorm.sSup_apply (bddAbove_representationSeminorms A), iSup]
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
  let p : Seminorm ℂ (LinearAlgebra.FreeProduct ℂ A) :=
    (normSeminorm ℂ (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)).comp
      (π.restrictLinearIsometry hV : LinearAlgebra.FreeProduct ℂ A →ₗ[ℂ]
        (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2))
  have hp : p ∈ representationSeminorms A := ⟨ι, π.restrictLinearIsometry hV, rfl⟩
  have hle : p ≤ seminorm A := le_csSup (bddAbove_representationSeminorms A) hp
  have hι : ‖π.restrictLinearIsometry hV x‖ ≤ seminorm A x := hle x
  rw [← π.restrictLinearIsometry_apply hV x η, V.norm_map, V.norm_map]
  exact (π.restrictLinearIsometry hV x).le_of_opNorm_le hι η

/-- Every unital `⋆`-homomorphism from `LinearAlgebra.FreeProduct ℂ A` into any unital C⋆-algebra
`B` (in any universe `w`) is bounded by `FullFreeProduct.seminorm A`. -/
theorem norm_starAlgHom_le_seminorm {B : Type w} [CStarAlgebra B]
    (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) (x : LinearAlgebra.FreeProduct ℂ A) :
    ‖ρ x‖ ≤ seminorm A x := by
  refine TauCeti.CStarAlgebra.norm_le_iff_forall_isNondegenerate.2 fun H _ _ _ σ hσ => ?_
  have hσ1 : σ 1 = 1 := hσ.ext fun b => by rw [← map_mul, one_mul, one_mul]
  let σu : B →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    { toFun := σ
      map_one' := hσ1
      map_mul' := map_mul σ
      map_zero' := map_zero σ
      map_add' := map_add σ
      commutes' c := by
        rw [Algebra.algebraMap_eq_smul_one, map_smul, hσ1, Algebra.algebraMap_eq_smul_one]
      map_star' := map_star σ }
  exact norm_representation_le_seminorm (σu.comp ρ) x

/-- Characterization of `seminorm A x ≤ c` via `ℓ²` representations in universe `max u v`. -/
theorem seminorm_le_iff_lp {x : LinearAlgebra.FreeProduct ℂ A} {c : ℝ} :
    seminorm A x ≤ c ↔
      ∀ (ι : Type (max u v))
        (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ]
          (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)), ‖π x‖ ≤ c :=
  ⟨fun h ι π => (norm_representation_le_seminorm π x).trans h, fun h => by
    rw [seminorm, Seminorm.sSup_apply (bddAbove_representationSeminorms A)]
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

theorem seminorm_mul_le (x y : LinearAlgebra.FreeProduct ℂ A) :
    seminorm A (x * y) ≤ seminorm A x * seminorm A y := by
  refine seminorm_le_iff_lp.2 fun ι π => ?_
  rw [map_mul]
  exact (norm_mul_le _ _).trans (mul_le_mul (norm_representation_le_seminorm π x)
    (norm_representation_le_seminorm π y) (norm_nonneg _) (apply_nonneg (seminorm A) x))

@[simp]
theorem seminorm_star (x : LinearAlgebra.FreeProduct ℂ A) :
    seminorm A (star x) = seminorm A x := by
  have hle (y : LinearAlgebra.FreeProduct ℂ A) : seminorm A (star y) ≤ seminorm A y := by
    refine seminorm_le_iff_lp.2 fun ι π => ?_
    rw [map_star, ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
    exact norm_representation_le_seminorm π y
  exact le_antisymm (hle x) (by simpa using hle (star x))

theorem seminorm_star_mul_self (x : LinearAlgebra.FreeProduct ℂ A) :
    seminorm A (star x * x) = seminorm A x * seminorm A x := by
  refine le_antisymm ((seminorm_mul_le _ _).trans_eq (by rw [seminorm_star])) ?_
  have hsqrt : seminorm A x ≤ √(seminorm A (star x * x)) := by
    refine seminorm_le_iff_lp.2 fun ι π => ?_
    refine Real.le_sqrt_of_sq_le ?_
    rw [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
    exact norm_representation_le_seminorm π (star x * x)
  calc seminorm A x * seminorm A x
      ≤ √(seminorm A (star x * x)) * √(seminorm A (star x * x)) :=
        mul_le_mul hsqrt hsqrt (apply_nonneg _ x) (Real.sqrt_nonneg _)
    _ = seminorm A (star x * x) := Real.mul_self_sqrt (apply_nonneg _ _)

theorem seminorm_one_le : seminorm A 1 ≤ 1 :=
  seminorm_le_iff_lp.2 fun _ π => by
    rw [map_one, ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le

theorem seminorm_ι_le (i : I) (a : A i) : seminorm A (ι ℂ A i a) ≤ ‖a‖ :=
  seminorm_le_iff_lp.2 fun _ π => by
    rw [← ιStar_apply, ← StarAlgHom.comp_apply]
    exact NonUnitalStarAlgHom.norm_apply_le (π.comp (ιStar ℂ A i)).toNonUnitalStarAlgHom a

omit [DecidableEq I] in
private theorem exists_normalized_starPositiveFunctional [∀ i, Nontrivial (A i)] (b : ∀ i, A i) :
    ∃ φ : ∀ i, StarPositiveFunctional (A i),
      (∀ i, φ i 1 = 1) ∧ ∀ i, φ i (star (b i) * b i) = (‖star (b i) * b i‖ : ℂ) := by
  let ord : ∀ i, PartialOrder (A i) := fun i => CStarAlgebra.spectralOrder (A i)
  have sord : ∀ i, @StarOrderedRing (A i) _ (ord i) _ :=
    fun i => CStarAlgebra.spectralOrderedRing (A i)
  have hb_nonneg (i : I) : @LE.le (A i) (ord i).toLE 0 (star (b i) * b i) := by
    let _ := ord i
    have _ := sord i
    exact star_mul_self_nonneg (b i)
  choose ω hω1 _ hωb using fun i =>
    @TauCeti.CStarAlgebra.exists_positiveContinuousLinearMap_apply_eq_norm (A i) _ (ord i) (sord i)
      _ (star (b i) * b i) (hb_nonneg i)
  refine ⟨fun i => @StarPositiveFunctional.ofPositiveLinearMap (A i) _ (ord i) _ (sord i) _
      (ω i).toPositiveLinearMap,
    fun i => (StarPositiveFunctional.ofPositiveLinearMap_apply _ 1).trans (hω1 i),
    fun i => (StarPositiveFunctional.ofPositiveLinearMap_apply _ _).trans (hωb i)⟩

/-- When every factor C⋆-algebra `A i` is nontrivial, the universal C⋆-seminorm is isometric on
each canonical factor map `ι ℂ A i₀`. No faithful state on any factor is required: we pair a
norm-attaining state for `star a * a` on `A i₀` with arbitrary states on the remaining factors in
the reduced free-product GNS representation. -/
@[simp]
theorem seminorm_ι [∀ i, Nontrivial (A i)] (i₀ : I) (a : A i₀) :
    seminorm A (ι ℂ A i₀ a) = ‖a‖ := by
  refine le_antisymm (seminorm_ι_le i₀ a) ?_
  let b : ∀ i, A i := fun i => if h : i = i₀ then h ▸ a else 1
  obtain ⟨φ, hφ, hφb⟩ := exists_normalized_starPositiveFunctional b
  let π := ReducedFreeProduct.representation φ hφ
  let Ω := ReducedFreeProduct.vacuum φ hφ
  have hb₀ : b i₀ = a := by simp [b]
  have hω₀ : φ i₀ (star a * a) = (‖star a * a‖ : ℂ) := by simpa [hb₀] using hφb i₀
  have hsq : ‖π (ι ℂ A i₀ a) Ω‖ ^ 2 = ‖a‖ ^ 2 := by
    rw [π.norm_sq_apply_eq_re_inner_star_mul Ω (ι ℂ A i₀ a), star_ι, ← map_mul (ι ℂ A i₀)]
    have hinner : ⟪Ω, π (ι ℂ A i₀ (star a * a)) Ω⟫_ℂ = φ i₀ (star a * a) := by
      rw [← ReducedFreeProduct.coe_ofAlgebraic φ hφ, ← ReducedFreeProduct.state_apply φ hφ,
        ReducedFreeProduct.state_ofAlgebraic, freeProductPositiveFunctional_ι]
    rw [hinner, hω₀]
    exact (Complex.ofReal_re ‖star a * a‖).trans (by rw [CStarRing.norm_star_mul_self, sq])
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
  obtain ⟨φ, hφ, _⟩ := exists_normalized_starPositiveFunctional (A := A) (fun _ => 1)
  let π := ReducedFreeProduct.representation φ hφ
  let Ω := ReducedFreeProduct.vacuum φ hφ
  calc (1 : ℝ) = ‖Ω‖ := (ReducedFreeProduct.norm_vacuum φ hφ).symm
    _ = ‖π 1 Ω‖ := by rw [map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
    _ ≤ ‖π 1‖ * ‖Ω‖ := (π 1).le_opNorm Ω
    _ = ‖π 1‖ := by rw [ReducedFreeProduct.norm_vacuum φ hφ, mul_one]
    _ ≤ seminorm A 1 := norm_representation_le_seminorm π 1

end SeminormAPI

end FullFreeProduct

/-- Type synonym of `LinearAlgebra.FreeProduct ℂ A` equipped with the universal C⋆-seminorm
`FullFreeProduct.seminorm A`. Its Hausdorff uniform completion is `FullFreeProduct A`. -/
@[expose] def FullAlgebraicFreeProduct : Type (max u v) :=
  LinearAlgebra.FreeProduct ℂ A

namespace FullAlgebraicFreeProduct

variable {A}

/-- Regard an algebraic free-product element as an element of `FullAlgebraicFreeProduct A`. -/
def toFull : LinearAlgebra.FreeProduct ℂ A ≃ FullAlgebraicFreeProduct A :=
  Equiv.refl _

/-- Underlying element of `LinearAlgebra.FreeProduct ℂ A`. -/
def ofFull : FullAlgebraicFreeProduct A ≃ LinearAlgebra.FreeProduct ℂ A :=
  Equiv.refl _

@[simp]
theorem toFull_symm : (toFull (A := A)).symm = ofFull :=
  (rfl)

@[simp]
theorem ofFull_symm : (ofFull (A := A)).symm = toFull :=
  (rfl)

@[simp]
theorem ofFull_toFull (x : LinearAlgebra.FreeProduct ℂ A) : ofFull (toFull x) = x :=
  (rfl)

@[simp]
theorem toFull_ofFull (x : FullAlgebraicFreeProduct A) : toFull (ofFull x) = x :=
  (rfl)

instance : Ring (FullAlgebraicFreeProduct A) :=
  inferInstanceAs (Ring (LinearAlgebra.FreeProduct ℂ A))

instance : Algebra ℂ (FullAlgebraicFreeProduct A) :=
  inferInstanceAs (Algebra ℂ (LinearAlgebra.FreeProduct ℂ A))

instance : StarRing (FullAlgebraicFreeProduct A) :=
  inferInstanceAs (StarRing (LinearAlgebra.FreeProduct ℂ A))

instance : StarModule ℂ (FullAlgebraicFreeProduct A) :=
  inferInstanceAs (StarModule ℂ (LinearAlgebra.FreeProduct ℂ A))

@[simp] theorem toFull_zero : toFull (0 : LinearAlgebra.FreeProduct ℂ A) = 0 := (rfl)
@[simp] theorem toFull_one : toFull (1 : LinearAlgebra.FreeProduct ℂ A) = 1 := (rfl)
@[simp] theorem toFull_add (x y : LinearAlgebra.FreeProduct ℂ A) :
    toFull (x + y) = toFull x + toFull y := (rfl)
@[simp] theorem toFull_neg (x : LinearAlgebra.FreeProduct ℂ A) :
    toFull (-x) = -toFull x := (rfl)
@[simp] theorem toFull_sub (x y : LinearAlgebra.FreeProduct ℂ A) :
    toFull (x - y) = toFull x - toFull y := (rfl)
@[simp] theorem toFull_mul (x y : LinearAlgebra.FreeProduct ℂ A) :
    toFull (x * y) = toFull x * toFull y := (rfl)
@[simp] theorem toFull_smul (c : ℂ) (x : LinearAlgebra.FreeProduct ℂ A) :
    toFull (c • x) = c • toFull x := (rfl)
@[simp] theorem toFull_star (x : LinearAlgebra.FreeProduct ℂ A) :
    toFull (star x) = star (toFull x) := (rfl)

@[simp] theorem ofFull_zero : ofFull (0 : FullAlgebraicFreeProduct A) = 0 := (rfl)
@[simp] theorem ofFull_one : ofFull (1 : FullAlgebraicFreeProduct A) = 1 := (rfl)
@[simp] theorem ofFull_add (x y : FullAlgebraicFreeProduct A) :
    ofFull (x + y) = ofFull x + ofFull y := (rfl)
@[simp] theorem ofFull_neg (x : FullAlgebraicFreeProduct A) :
    ofFull (-x) = -ofFull x := (rfl)
@[simp] theorem ofFull_sub (x y : FullAlgebraicFreeProduct A) :
    ofFull (x - y) = ofFull x - ofFull y := (rfl)
@[simp] theorem ofFull_mul (x y : FullAlgebraicFreeProduct A) :
    ofFull (x * y) = ofFull x * ofFull y := (rfl)
@[simp] theorem ofFull_smul (c : ℂ) (x : FullAlgebraicFreeProduct A) :
    ofFull (c • x) = c • ofFull x := (rfl)
@[simp] theorem ofFull_star (x : FullAlgebraicFreeProduct A) :
    ofFull (star x) = star (ofFull x) := (rfl)

variable (A) in
/-- `FullAlgebraicFreeProduct.toFull` as a unital `⋆`-algebra equivalence. -/
def toFullStarAlgEquiv : LinearAlgebra.FreeProduct ℂ A ≃⋆ₐ[ℂ] FullAlgebraicFreeProduct A where
  __ := toFull
  map_mul' _ _ := (rfl)
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)
  map_star' _ := (rfl)

@[simp]
theorem toFullStarAlgEquiv_apply (x : LinearAlgebra.FreeProduct ℂ A) :
    toFullStarAlgEquiv A x = toFull x :=
  (rfl)

@[simp]
theorem toFullStarAlgEquiv_symm_apply (x : FullAlgebraicFreeProduct A) :
    (toFullStarAlgEquiv A).symm x = ofFull x :=
  (rfl)

instance : SeminormedAddCommGroup (FullAlgebraicFreeProduct A) :=
  @AddGroupSeminorm.toSeminormedAddCommGroup (FullAlgebraicFreeProduct A) _
    (FullFreeProduct.seminorm A).toAddGroupSeminorm

@[simp]
theorem norm_toFull (x : LinearAlgebra.FreeProduct ℂ A) :
    ‖toFull x‖ = FullFreeProduct.seminorm A x :=
  (rfl)

theorem norm_def (x : FullAlgebraicFreeProduct A) :
    ‖x‖ = FullFreeProduct.seminorm A (ofFull x) :=
  (rfl)

instance : SeminormedRing (FullAlgebraicFreeProduct A) where
  __ : SeminormedAddCommGroup (FullAlgebraicFreeProduct A) := inferInstance
  __ : Ring (FullAlgebraicFreeProduct A) := inferInstance
  norm_mul_le x y := by
    simpa only [norm_def, ofFull_mul] using
      FullFreeProduct.seminorm_mul_le (ofFull x) (ofFull y)

instance : NormedAlgebra ℂ (FullAlgebraicFreeProduct A) where
  __ : Algebra ℂ (FullAlgebraicFreeProduct A) := inferInstance
  norm_smul_le c x := by
    simp only [norm_def, ofFull_smul]
    exact (map_smul_eq_mul _ _ _).le

instance : NormedStarGroup (FullAlgebraicFreeProduct A) where
  norm_star_le x := by
    simp only [norm_def, ofFull_star, FullFreeProduct.seminorm_star, le_refl]

instance [∀ i, Nontrivial (A i)] : NormOneClass (FullAlgebraicFreeProduct A) where
  norm_one := FullFreeProduct.seminorm_one

theorem norm_star_mul_self (x : FullAlgebraicFreeProduct A) : ‖star x * x‖ = ‖x‖ * ‖x‖ := by
  simpa only [norm_def, ofFull_mul, ofFull_star] using
    FullFreeProduct.seminorm_star_mul_self (ofFull x)

end FullAlgebraicFreeProduct

/-- The full unital C⋆-free product `*_{i : I} A i` of a family of unital C⋆-algebras `A i`: the
Hausdorff completion of `LinearAlgebra.FreeProduct ℂ A` in its universal C⋆-seminorm. -/
@[expose] def FullFreeProduct : Type (max u v) :=
  Completion (FullAlgebraicFreeProduct A)

namespace FullFreeProduct

open FullAlgebraicFreeProduct

instance : CStarAlgebra (Completion (FullAlgebraicFreeProduct A)) where
  norm_smul_le := norm_smul_le
  toCStarRing := Completion.cstarRing fun x => (FullAlgebraicFreeProduct.norm_star_mul_self x).ge

instance : CStarAlgebra (FullFreeProduct A) :=
  inferInstanceAs (CStarAlgebra (Completion (FullAlgebraicFreeProduct A)))

instance [∀ i, Nontrivial (A i)] : NormOneClass (FullFreeProduct A) :=
  inferInstanceAs (NormOneClass (Completion (FullAlgebraicFreeProduct A)))

/-- The canonical unital `⋆`-algebra homomorphism from the algebraic free product into the full
C⋆-free product, with dense range. -/
def ofAlgebraic : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] FullFreeProduct A where
  toFun x := (toFull x : Completion (FullAlgebraicFreeProduct A))
  map_one' := by
    rw [toFull_one]
    exact Completion.coe_one _
  map_mul' x y := Completion.coe_mul (toFull x) (toFull y)
  map_zero' := Completion.coe_zero
  map_add' x y := Completion.coe_add (toFull x) (toFull y)
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, toFull_smul, toFull_one, Completion.coe_smul,
      Completion.coe_one, ← Algebra.algebraMap_eq_smul_one]
    rfl
  map_star' x := Completion.coe_star (toFull x)

section CoreAPI

variable {A}

@[simp]
theorem norm_ofAlgebraic (x : LinearAlgebra.FreeProduct ℂ A) :
    ‖ofAlgebraic A x‖ = seminorm A x :=
  Completion.norm_coe (toFull x)

/-- The image of the algebraic free product is norm dense in `FullFreeProduct A`. -/
theorem denseRange_ofAlgebraic : DenseRange (ofAlgebraic A) :=
  Completion.denseRange_coe.comp toFull.surjective.denseRange (Completion.continuous_coe _)

/-- Closed properties on `FullFreeProduct A` follow from their restriction to
`LinearAlgebra.FreeProduct ℂ A`. -/
@[elab_as_elim]
theorem induction_on {p : FullFreeProduct A → Prop} (x : FullFreeProduct A)
    (hp : IsClosed {x | p x}) (ih : ∀ a, p (ofAlgebraic A a)) : p x :=
  Completion.induction_on (p := p) x hp fun a => ih (ofFull a)

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
  ContinuousLinearMap.ext fun x => induction_on x (isClosed_eq S.continuous T.continuous) h

open scoped _root_.CStarAlgebra in
/-- Unital `⋆`-homomorphisms from `FullFreeProduct A` into a C⋆-algebra are determined on
`ofAlgebraic A`. -/
theorem starAlgHom_ext_ofAlgebraic {B : Type w} [CStarAlgebra B]
    {Φ Ψ : FullFreeProduct A →⋆ₐ[ℂ] B} (h : Φ.comp (ofAlgebraic A) = Ψ.comp (ofAlgebraic A)) :
    Φ = Ψ :=
  StarAlgHom.ext fun x =>
    induction_on x (isClosed_eq (map_continuous Φ) (map_continuous Ψ)) fun a => congr($h a)

/-- Unital `⋆`-homomorphisms from `FullFreeProduct A` into a C⋆-algebra are determined by their
restrictions to the factors `factor i`. -/
@[ext]
theorem starAlgHom_ext {B : Type w} [CStarAlgebra B] {Φ Ψ : FullFreeProduct A →⋆ₐ[ℂ] B}
    (h : ∀ i a, Φ (factor i a) = Ψ (factor i a)) : Φ = Ψ :=
  starAlgHom_ext_ofAlgebraic <| LinearAlgebra.FreeProduct.starAlgHom_ext fun i a => by
    simpa only [StarAlgHom.comp_apply, ← factor_apply] using h i a

private def liftAlgebraicCLM {B : Type w} [CStarAlgebra B]
    (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) : FullAlgebraicFreeProduct A →L[ℂ] B :=
  ((ρ : LinearAlgebra.FreeProduct ℂ A →ₗ[ℂ] B).comp
    ((toFullStarAlgEquiv A).symm :
      FullAlgebraicFreeProduct A →ₗ[ℂ] LinearAlgebra.FreeProduct ℂ A)).mkContinuous 1 fun x => by
    simpa [FullAlgebraicFreeProduct.norm_def] using norm_starAlgHom_le_seminorm ρ (ofFull x)

private theorem fromCompletion_liftAlgebraicCLM_ofAlgebraic {B : Type w} [CStarAlgebra B]
    (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) (a : LinearAlgebra.FreeProduct ℂ A) :
    (liftAlgebraicCLM ρ).fromCompletion (ofAlgebraic A a) = ρ a :=
  (ContinuousLinearMap.fromCompletion_apply_coe (liftAlgebraicCLM ρ) (toFull a)).trans
    (by simp [liftAlgebraicCLM])

private def liftAlgebraicHom {B : Type w} [CStarAlgebra B]
    (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) : FullFreeProduct A →⋆ₐ[ℂ] B where
  toFun := (liftAlgebraicCLM ρ).fromCompletion
  map_one' := by
    rw [← map_one (ofAlgebraic A), fromCompletion_liftAlgebraicCLM_ofAlgebraic, map_one]
  map_mul' x y := by
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih a =>
      induction y using induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih b => simp only [← map_mul, fromCompletion_liftAlgebraicCLM_ofAlgebraic]
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' c := by
    rw [← AlgHomClass.commutes (ofAlgebraic A) c, fromCompletion_liftAlgebraicCLM_ofAlgebraic,
      AlgHomClass.commutes]
  map_star' x := by
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih a => simp only [← map_star, fromCompletion_liftAlgebraicCLM_ofAlgebraic]

/-- `FullFreeProduct A` is the universal unital C⋆-envelope of `LinearAlgebra.FreeProduct ℂ A`:
unital `⋆`-homomorphisms out of `LinearAlgebra.FreeProduct ℂ A` into any unital C⋆-algebra `B`
(in any universe `w`) correspond bijectively to unital `⋆`-homomorphisms out of
`FullFreeProduct A`. -/
def liftAlgebraic {B : Type w} [CStarAlgebra B] :
    (LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) ≃ (FullFreeProduct A →⋆ₐ[ℂ] B) where
  toFun := liftAlgebraicHom
  invFun Φ := Φ.comp (ofAlgebraic A)
  left_inv ρ := StarAlgHom.ext (fromCompletion_liftAlgebraicCLM_ofAlgebraic ρ)
  right_inv Φ :=
    starAlgHom_ext_ofAlgebraic
      (StarAlgHom.ext (fromCompletion_liftAlgebraicCLM_ofAlgebraic (Φ.comp (ofAlgebraic A))))

@[simp]
theorem liftAlgebraic_ofAlgebraic {B : Type w} [CStarAlgebra B]
    (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) (a : LinearAlgebra.FreeProduct ℂ A) :
    liftAlgebraic ρ (ofAlgebraic A a) = ρ a :=
  fromCompletion_liftAlgebraicCLM_ofAlgebraic ρ a

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
theorem continuous_liftRepresentation {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    Continuous (liftRepresentation π) :=
  map_continuous (liftRepresentation π)

theorem isClosed_setRange_liftRepresentation {H : Type w} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    IsClosed (Set.range (liftRepresentation π)) :=
  (liftRepresentation π).isClosed_setRange

theorem coe_range_liftRepresentation {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ((liftRepresentation π).range : Set (H →L[ℂ] H)) = Set.range (liftRepresentation π) :=
  (liftRepresentation π).toAlgHom.coe_range

/-- The range of `liftRepresentation π` is the norm closure of the algebraic image `π.range`. -/
theorem range_liftRepresentation {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (liftRepresentation π).range = π.range.topologicalClosure := by
  apply SetLike.ext'
  have hcoe : (π.range : Set (H →L[ℂ] H)) = Set.range π := π.toAlgHom.coe_range
  rw [coe_range_liftRepresentation, StarSubalgebra.topologicalClosure_coe, hcoe]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    refine induction_on x (isClosed_closure.preimage (continuous_liftRepresentation π)) fun a => ?_
    rw [liftRepresentation_ofAlgebraic]
    exact subset_closure ⟨a, rfl⟩
  · refine (isClosed_setRange_liftRepresentation π).closure_subset_iff.mpr ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨ofAlgebraic A a, liftRepresentation_ofAlgebraic π a⟩

instance isClosed_ker_liftRepresentation {H : Type w} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    IsClosed (TwoSidedIdeal.ker (liftRepresentation π) : Set (FullFreeProduct A)) :=
  NonUnitalStarAlgHom.isClosed_ker (liftRepresentation π)

/-- First isometric `⋆`-isomorphism theorem for the extended Hilbert-space representation
`liftRepresentation π`. -/
def quotientKerEquivRangeLiftRepresentation {H : Type w} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    FullFreeProduct A ⧸ TwoSidedIdeal.ker (liftRepresentation π) ≃⋆ₐ[ℂ]
      (liftRepresentation π).range :=
  (liftRepresentation π).quotientKerEquivRange

theorem coe_quotientKerEquivRangeLiftRepresentation_mk {H : Type w} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) (x : FullFreeProduct A) :
    (quotientKerEquivRangeLiftRepresentation π
      (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker (liftRepresentation π)) x) : H →L[ℂ] H) =
      liftRepresentation π x :=
  (liftRepresentation π).coe_quotientKerEquivRange_mk x

private def pullSubalgebraState {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ω : S →ₚ[ℂ] ℂ)
    (f : FullFreeProduct A →⋆ₐ[ℂ] S) : StarPositiveFunctional (FullFreeProduct A) where
  toLinearMap := ω.toLinearMap.comp f.toAlgHom.toLinearMap
  square_nonneg x := by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom,
      map_mul, map_star]
    exact ω.map_nonneg (Subtype.coe_le_coe.mp (star_mul_self_nonneg (f x : H →L[ℂ] H)))

private theorem pullSubalgebraState_apply {H : Type w} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (ω : S →ₚ[ℂ] ℂ) (f : FullFreeProduct A →⋆ₐ[ℂ] S) (x : FullFreeProduct A) :
    pullSubalgebraState S ω f x = ω (f x) :=
  (rfl)

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
theorem mapEquiv_factor {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (e : (i : I) → A i ≃⋆ₐ[ℂ] A' i) (i : I) (a : A i) :
    mapEquiv e (factor i a) = factor i (e i a) := by
  simp [mapEquiv, factor_apply]

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

/-- Relabeling the index type along an equivalence `σ : J ≃ I` induces an isometric `⋆`-isomorphism
of full C⋆-free products. -/
def reindexEquiv {J : Type*} [DecidableEq J] (σ : J ≃ I) :
    FullFreeProduct (fun j => A (σ j)) ≃⋆ₐ[ℂ] FullFreeProduct A :=
  congrAlgebraic (reindexStarAlgEquiv ℂ A σ)

@[simp]
theorem reindexEquiv_factor {J : Type*} [DecidableEq J] (σ : J ≃ I) (j : J) (a : A (σ j)) :
    reindexEquiv A σ (factor (A := fun k => A (σ k)) j a) = factor (A := A) (σ j) a := by
  simp [reindexEquiv, factor_apply]

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
  unfold reducedRepresentation
  apply SetLike.ext'
  rw [coe_range_liftRepresentation]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    refine induction_on x ((ReducedFreeProduct.isClosed_algebra φ hφ).preimage
      (continuous_liftRepresentation (ReducedFreeProduct.representation φ hφ))) fun a => ?_
    rw [liftRepresentation_ofAlgebraic]
    exact (ReducedFreeProduct.mem_algebra_iff φ hφ _).mpr (subset_closure ⟨a, rfl⟩)
  · intro T hT
    refine (isClosed_setRange_liftRepresentation
      (ReducedFreeProduct.representation φ hφ)).closure_subset_iff.mpr ?_
      ((ReducedFreeProduct.mem_algebra_iff φ hφ T).mp hT)
    rintro _ ⟨a, rfl⟩
    exact ⟨ofAlgebraic A a,
      liftRepresentation_ofAlgebraic (ReducedFreeProduct.representation φ hφ) a⟩

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
    toReduced φ hφ (ofAlgebraic A x) = ReducedFreeProduct.ofAlgebraic φ hφ x :=
  Subtype.ext <| (coe_toReduced φ hφ (ofAlgebraic A x)).trans <|
    (reducedRepresentation_ofAlgebraic φ hφ x).trans
      (ReducedFreeProduct.coe_ofAlgebraic φ hφ x).symm

@[simp]
theorem toReduced_factor (i : I) (a : A i) :
    toReduced φ hφ (factor i a) = ReducedFreeProduct.factor φ hφ i a :=
  (congrArg (toReduced φ hφ) (factor_apply i a)).trans <|
    (toReduced_ofAlgebraic φ hφ (ι ℂ A i a)).trans
      (ReducedFreeProduct.factor_apply φ hφ i a).symm

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

instance isClosed_ker_reducedRepresentation :
    IsClosed (TwoSidedIdeal.ker (reducedRepresentation φ hφ) : Set (FullFreeProduct A)) :=
  isClosed_ker_liftRepresentation (ReducedFreeProduct.representation φ hφ)

instance isClosed_ker_toReduced :
    IsClosed (TwoSidedIdeal.ker (toReduced φ hφ) : Set (FullFreeProduct A)) :=
  (ker_toReduced φ hφ).symm ▸ isClosed_ker_reducedRepresentation φ hφ

/-- First `⋆`-isomorphism theorem identifying `ReducedFreeProduct.algebra φ hφ` with the
C⋆-quotient of `FullFreeProduct A` by `TwoSidedIdeal.ker (toReduced φ hφ)`. -/
def quotientKerToReducedEquiv :
    FullFreeProduct A ⧸ TwoSidedIdeal.ker (toReduced φ hφ) ≃⋆ₐ[ℂ]
      ReducedFreeProduct.algebra φ hφ :=
  ((TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq (ker_toReduced φ hφ)).trans
    (quotientKerEquivRangeLiftRepresentation (ReducedFreeProduct.representation φ hφ))).trans
    { toFun x := ⟨x.1, range_reducedRepresentation φ hφ ▸ x.2⟩
      invFun x := ⟨x.1, (range_reducedRepresentation φ hφ).symm ▸ x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      map_star' _ := rfl }

theorem quotientKerToReducedEquiv_mk (x : FullFreeProduct A) :
    quotientKerToReducedEquiv φ hφ
      (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker (toReduced φ hφ)) x) = toReduced φ hφ x :=
  Subtype.ext <|
    (congrArg Subtype.val (congrArg
      (quotientKerEquivRangeLiftRepresentation (ReducedFreeProduct.representation φ hφ))
      (TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq_mk (ker_toReduced φ hφ) x))).trans
      (coe_quotientKerEquivRangeLiftRepresentation_mk (ReducedFreeProduct.representation φ hφ) x)

/-- The vacuum positive functional on `FullFreeProduct A` pulled back from
`ReducedFreeProduct.state φ hφ` along `toReduced φ hφ`. -/
def state : StarPositiveFunctional (FullFreeProduct A) :=
  pullSubalgebraState (ReducedFreeProduct.algebra φ hφ)
    (ReducedFreeProduct.state φ hφ) (toReduced φ hφ)

theorem state_apply_eq_reduced (x : FullFreeProduct A) :
    state φ hφ x = ReducedFreeProduct.state φ hφ (toReduced φ hφ x) :=
  pullSubalgebraState_apply (ReducedFreeProduct.algebra φ hφ)
    (ReducedFreeProduct.state φ hφ) (toReduced φ hφ) x

@[simp]
theorem state_ofAlgebraic (x : LinearAlgebra.FreeProduct ℂ A) :
    state φ hφ (ofAlgebraic A x) = freeProductPositiveFunctional φ hφ x :=
  (state_apply_eq_reduced φ hφ (ofAlgebraic A x)).trans <|
    (congrArg (ReducedFreeProduct.state φ hφ) (toReduced_ofAlgebraic φ hφ x)).trans
      (ReducedFreeProduct.state_ofAlgebraic φ hφ x)

@[simp]
theorem state_one : state φ hφ 1 = 1 :=
  (congrArg (state φ hφ) (ofAlgebraic A).map_one.symm).trans <|
    (state_ofAlgebraic φ hφ 1).trans (freeProductPositiveFunctional_one φ hφ)

@[simp]
theorem state_factor (i : I) (a : A i) : state φ hφ (factor i a) = φ i a :=
  (congrArg (state φ hφ) (factor_apply i a)).trans <|
    (state_ofAlgebraic φ hφ (ι ℂ A i a)).trans (freeProductPositiveFunctional_ι φ hφ i a)

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
      exact (state_ofAlgebraic φ hφ x).trans (freeProductPositiveFunctional_apply φ hφ x))
  have hranges : (fun i => (factor (A := A) i).toAlgHom.range) =
      (fun i => ((ι ℂ A i).range).map (ofAlgebraic A).toAlgHom) := by
    funext i
    simpa only [factor, StarAlgHom.comp, ιStar_toAlgHom] using
      AlgHom.range_comp (ι ℂ A i) (ofAlgebraic A).toAlgHom
  simpa only [← hranges] using h

end ReducedQuotientAndState

end FullFreeProduct

end SeminormAndCompletion

end TauCeti
