/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import TauCeti.RingTheory.FormalGroup.LazardRing.Independence
-- Proof-only: maps out of a polynomial ring lift along surjections, and `ker_constantCoeff`.
import TauCeti.Algebra.MvPolynomial.Lift
import TauCeti.RingTheory.MvPolynomial.Ideal
-- Proof-only: injective graded ring homomorphisms reflect homogeneity.
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Maps
-- Proof-only: the graded Nakayama lemma for generators.
import TauCeti.RingTheory.GradedAlgebra.Nakayama
-- Proof-only: `ker_constantCoeff` identifies the augmentation ideal with `idealOfVars`.
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Lazard's theorem: the Lazard ring is a polynomial ring

The Lazard ring `L` is the polynomial ring `ℤ[x₁, x₂, …]` on the generators
`xₙ = TauCeti.LazardRing.generator n` of degree `2n`.

The generators are algebraically independent (`TauCeti.LazardRing.algebraicIndependent_generator`).
They also generate `L` as a ring: `L` is connected (`L₀ = ℤ`), its augmentation ideal `I` is the
irrelevant ideal `⨁_{n > 0} Lₙ`, and the classes of the `xₙ` form a basis of the indecomposables
`I ⧸ I²` (`TauCeti.LazardRing.cotangentBasis`). By the graded Nakayama lemma
(`TauCeti.GradedAlgebra.adjoin_eq_top_of_irrelevant_le`), homogeneous elements of positive degree
whose classes generate `I ⧸ I²` generate `L` over `L₀ = ℤ`.

The resulting isomorphism `ℤ[x₁, x₂, …] ≃ₐ[ℤ] L` is graded when `xₖ` is given degree `2k`, and
identifies the augmentation ideal and its powers with the ideal of variables and its powers. In
particular `L` is an integral domain, and any homogeneous element of degree `m` in `I²` involves
only variables `X k` with `2k < m`, so a degree-`2n` element congruent to `c • xₙ` modulo `I²`
corresponds to `c • X n` plus a polynomial in variables of index strictly below `n`.

A ring homomorphism `L →+* R`, and hence a commutative formal group law over `R`, is therefore the
same as a family `(vₙ)` of elements of `R`, the values of the generators
(`TauCeti.LazardRing.homEquiv`). We call them the Lazard coordinates of the law.

Since `L` is a polynomial ring, ring homomorphisms out of `L` lift along surjective ring
homomorphisms (`MvPolynomial.exists_comp_eq_of_surjective`). By the universal property of `L`,
every commutative formal group law over `S` is therefore the base change of a commutative formal
group law over `R` along any surjection `R →+* S`. This is the use Lubin and Tate make of Lazard's
theorem: commutative formal group laws over `A ⧸ I` lift to `A`, so deformations of a commutative
formal group law exist over every ring surjecting onto its coefficient ring.

## Main definitions

* `TauCeti.LazardRing.mvPolynomialEquiv`: the isomorphism `ℤ[x₁, x₂, …] ≃ₐ[ℤ] L` sending `xₙ` to
  the generator `xₙ`.
* `TauCeti.LazardRing.homEquiv`: ring homomorphisms `L →+* R` are families `ℕ+ → R`, by their
  values on the generators (the Lazard coordinates).

## Main results

* `TauCeti.LazardRing.adjoin_range_generator`: the generators `xₙ` generate `L` as a ring.
* `TauCeti.LazardRing.ringHom_ext`: a ring homomorphism out of `L` is determined by its values on
  the generators.
* `TauCeti.LazardRing.augmentation_mvPolynomialEquiv` and
  `TauCeti.LazardRing.augmentationIdeal_eq_span_generator`: under `ℤ[x₁, x₂, …] ≃ₐ[ℤ] L`, the
  augmentation is `constantCoeff`, `L` is an integral domain, and the augmentation ideal is
  spanned by the generators `xₙ`.
* `TauCeti.LazardRing.hurewicz_injective`: the Hurewicz homomorphism `L →+* ℤ[b₁, b₂, …]` is
  injective.
* `TauCeti.LazardRing.mvPolynomialEquiv_mem_grading_iff`: the isomorphism carries the polynomials
  that are homogeneous of degree `n`, for `xₖ` of degree `2k`, onto `Lₙ`.
* `TauCeti.LazardRing.mvPolynomialEquiv_mem_pow_augmentationIdeal_iff`: the isomorphism carries the
  powers of the ideal of variables onto the powers of the augmentation ideal.
* `TauCeti.LazardRing.two_mul_lt_of_mem_vars_mvPolynomialEquiv_symm` and
  `TauCeti.LazardRing.lt_of_mem_vars_mvPolynomialEquiv_symm_sub_smul_X`: homogeneous decomposable
  elements in degree `m` involve only variables `X k` with `2k < m`, so lifts of `c • xₙ` modulo
  `I²` in `L₂ₙ` differ from `c • X n` by polynomials in variables below `n`.
* `TauCeti.LazardRing.exists_comp_eq_of_surjective`: a ring homomorphism `L →+* S` factors
  through any surjective ring homomorphism `R →+* S`.
* `FormalGroup.exists_map_eq_of_surjective`: a commutative formal group law over `S` is the base
  change of a commutative formal group law over `R` along any surjective `R →+* S`.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* J. F. Adams, *Stable Homotopy and Generalised Homology*, Part II, §7.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1
  (Lazard's theorem A2.1.8).
* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966).
-/

public section

noncomputable section

namespace TauCeti.LazardRing

/-- Lifts of a basis of the indecomposables generate the augmentation ideal modulo its square: the
augmentation ideal lies in the ideal generated by the generators `xₙ` plus `I²`. -/
private theorem augmentationIdeal_le_span_generator_sup_sq :
    augmentationIdeal ≤ Ideal.span (Set.range generator) ⊔ augmentationIdeal ^ 2 := by
  intro y hy
  -- Lift the coordinates of the class of `y` in the basis of `I ⧸ I²` to a combination `z` of
  -- the generators.
  set z : augmentationIdeal := (cotangentBasis.repr (augmentationIdeal.toCotangent ⟨y, hy⟩)).sum
    fun n k ↦ k • ⟨generator n, generator_mem_augmentationIdeal n⟩
  have hzspan : (z : LazardRing) ∈ Ideal.span (Set.range generator) := by
    simp only [z, Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul_of_tower]
    exact sum_mem fun n _ ↦ Submodule.smul_of_tower_mem _ _ (Ideal.subset_span ⟨n, rfl⟩)
  exact Submodule.mem_sup.2 ⟨z, hzspan, y - z, sub_sum_generator_mem_sq hy, add_sub_cancel _ _⟩

/-- **Lazard's theorem, generation**: the generators `xₙ ∈ L₂ₙ` generate the Lazard ring as a
ring. -/
theorem adjoin_range_generator : Algebra.adjoin ℤ (Set.range generator) = ⊤ := by
  have h := GradedAlgebra.adjoin_eq_top_of_irrelevant_le grading
    (s := Set.range generator) (by
      rintro _ ⟨n, rfl⟩
      exact ⟨2 * n, by positivity, generator_mem_grading n⟩)
    (by simpa only [← augmentationIdeal_eq_irrelevant] using
      augmentationIdeal_le_span_generator_sup_sq)
  -- Over `L₀ = ℤ`, the subalgebra generated over `L₀` is the subalgebra generated over `ℤ`.
  rw [eq_top_iff]
  rintro x -
  have hx : x ∈ Algebra.adjoin (grading 0) (Set.range generator) := h ▸ trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    rw [SetLike.GradeZero.algebraMap_apply, ← intCast_augmentation_of_mem_grading_zero r.property]
    exact intCast_mem _ _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

/-- **Lazard's theorem**: the Lazard ring is the polynomial ring `ℤ[x₁, x₂, …]` on the generators
`xₙ = TauCeti.LazardRing.generator n`. The isomorphism is evaluation at the generators. -/
def mvPolynomialEquiv : MvPolynomial ℕ+ ℤ ≃ₐ[ℤ] LazardRing :=
  AlgEquiv.ofBijective (MvPolynomial.aeval generator)
    ⟨algebraicIndependent_iff_injective_aeval.1 algebraicIndependent_generator, by
      rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, adjoin_range_generator]⟩

/-- The isomorphism `ℤ[x₁, x₂, …] ≃ₐ[ℤ] L` is evaluation at the generators. -/
theorem mvPolynomialEquiv_apply (p : MvPolynomial ℕ+ ℤ) :
    mvPolynomialEquiv p = MvPolynomial.aeval generator p :=
  (rfl)

/-- The isomorphism `ℤ[x₁, x₂, …] ≃ₐ[ℤ] L` sends the variable `xₙ` to the generator `xₙ`. -/
@[simp]
theorem mvPolynomialEquiv_X (n : ℕ+) : mvPolynomialEquiv (MvPolynomial.X n) = generator n := by
  simp [mvPolynomialEquiv_apply]

/-- The inverse isomorphism `L ≃ₐ[ℤ] ℤ[x₁, x₂, …]` sends the generator `xₙ` to the variable `xₙ`. -/
@[simp]
theorem mvPolynomialEquiv_symm_generator (n : ℕ+) :
    mvPolynomialEquiv.symm (generator n) = MvPolynomial.X n := by
  rw [AlgEquiv.symm_apply_eq, mvPolynomialEquiv_X]

section homEquiv

variable {R : Type*} [CommRing R]

/-- **Lazard coordinates.** Ring homomorphisms out of the Lazard ring `L = ℤ[x₁, x₂, …]` are the
same as families of elements indexed by the generators: `φ` corresponds to `n ↦ φ xₙ`. -/
def homEquiv : (LazardRing →+* R) ≃ (ℕ+ → R) where
  toFun φ n := φ (generator n)
  invFun v := (MvPolynomial.eval₂Hom (Int.castRingHom R) v).comp
    (mvPolynomialEquiv.symm : LazardRing →+* MvPolynomial ℕ+ ℤ)
  left_inv φ := by
    have h : MvPolynomial.eval₂Hom (Int.castRingHom R) (fun n ↦ φ (generator n)) =
        φ.comp (mvPolynomialEquiv : MvPolynomial ℕ+ ℤ →+* LazardRing) :=
      MvPolynomial.ringHom_ext (fun _ ↦ by simp) (fun _ ↦ by simp)
    ext x
    simp [h]
  right_inv v := funext fun n ↦ by simp

@[simp]
theorem homEquiv_apply (φ : LazardRing →+* R) (n : ℕ+) : homEquiv φ n = φ (generator n) :=
  (rfl)

/-- The homomorphism with Lazard coordinates `v` evaluates a polynomial in the generators at `v`. -/
theorem homEquiv_symm_apply (v : ℕ+ → R) (x : LazardRing) :
    homEquiv.symm v x =
      MvPolynomial.eval₂Hom (Int.castRingHom R) v (mvPolynomialEquiv.symm x) :=
  (rfl)

/-- The homomorphism with Lazard coordinates `v` sends the generator `xₙ` to `v n`. -/
@[simp]
theorem homEquiv_symm_apply_generator (v : ℕ+ → R) (n : ℕ+) :
    homEquiv.symm v (generator n) = v n := by
  simp [homEquiv_symm_apply]

/-- A ring homomorphism out of the Lazard ring is determined by its values on the generators. -/
@[ext]
theorem ringHom_ext {φ ψ : LazardRing →+* R} (h : ∀ n, φ (generator n) = ψ (generator n)) :
    φ = ψ :=
  homEquiv.injective (funext h)

/-- The Lazard coordinates of a base change are the images of the Lazard coordinates. -/
theorem comp_homEquiv_symm {S : Type*} [CommRing S] (g : R →+* S) (v : ℕ+ → R) :
    g.comp (homEquiv.symm v) = homEquiv.symm (g ∘ v) :=
  ringHom_ext fun n ↦ by simp

end homEquiv

/-- The Lazard ring is an integral domain, transferred from `ℤ[x₁, x₂, …]` via Lazard's polynomial
presentation (`TauCeti.LazardRing.mvPolynomialEquiv`). -/
instance : IsDomain LazardRing :=
  mvPolynomialEquiv.symm.toMulEquiv.isDomain

/-- Under `ℤ[x₁, x₂, …] ≃ₐ[ℤ] L`, the augmentation of `L` is the constant coefficient. -/
@[simp]
theorem augmentation_mvPolynomialEquiv (p : MvPolynomial ℕ+ ℤ) :
    augmentation (mvPolynomialEquiv p) = MvPolynomial.constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [mvPolynomialEquiv_apply, MvPolynomial.aeval_C, MvPolynomial.constantCoeff_C]
    simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n _ =>
    rw [map_mul, mvPolynomialEquiv_X, map_mul, mem_augmentationIdeal.mp
      (generator_mem_augmentationIdeal n), mul_zero, map_mul, MvPolynomial.constantCoeff_X,
      mul_zero]

/-- Under `L ≃ₐ[ℤ] ℤ[x₁, x₂, …]`, the constant coefficient is the augmentation. -/
@[simp]
theorem constantCoeff_mvPolynomialEquiv_symm (x : LazardRing) :
    MvPolynomial.constantCoeff (mvPolynomialEquiv.symm x) = augmentation x := by
  rw [← augmentation_mvPolynomialEquiv, AlgEquiv.apply_symm_apply]

/-- The augmentation ideal of the Lazard ring is spanned by the polynomial generators `xₙ`. -/
theorem augmentationIdeal_eq_span_generator :
    augmentationIdeal = Ideal.span (Set.range generator) := by
  let f : MvPolynomial ℕ+ ℤ →+* LazardRing := mvPolynomialEquiv
  have hmap : (MvPolynomial.idealOfVars ℕ+ ℤ).map f = Ideal.span (Set.range generator) := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
    simp [f, Function.comp_def]
  rw [← hmap]
  ext x
  rw [mem_augmentationIdeal, ← constantCoeff_mvPolynomialEquiv_symm, ← RingHom.mem_ker,
    MvPolynomial.ker_constantCoeff, Ideal.mem_map_iff_of_surjective f mvPolynomialEquiv.surjective]
  exact ⟨fun hx ↦ ⟨mvPolynomialEquiv.symm x, hx, mvPolynomialEquiv.apply_symm_apply x⟩,
    fun ⟨q, hq, hqx⟩ ↦ by simpa [f, ← hqx] using hq⟩

/-- **The Hurewicz homomorphism of the Lazard ring is injective**: the homomorphism
`L →+* ℤ[b₁, b₂, …]` classifying the additive formal group law transported along the strict
coordinate `X + ∑ bᵢ X^(i + 1)` embeds `L` in `ℤ[b₁, b₂, …]`. -/
theorem hurewicz_injective : Function.Injective hurewicz := by
  -- Through `L ≃ ℤ[x₁, x₂, …]`, the Hurewicz homomorphism is evaluation at the images of the `xₙ`.
  have h (p : MvPolynomial ℕ+ ℤ) :
      hurewicz (mvPolynomialEquiv p) = MvPolynomial.aeval (hurewicz ∘ generator) p := by
    rw [mvPolynomialEquiv_apply]
    exact MvPolynomial.comp_aeval_apply generator hurewicz.toIntAlgHom p
  intro x y hxy
  apply mvPolynomialEquiv.symm.injective
  apply algebraicIndependent_iff_injective_aeval.1 algebraicIndependent_hurewicz_generator
  rw [← h, ← h, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, hxy]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- **Lazard's theorem, graded**: giving the variable `xₖ` the degree `2k`, the isomorphism
`ℤ[x₁, x₂, …] ≃ₐ[ℤ] L` carries the polynomials that are homogeneous of degree `n` exactly onto
the degree-`n` part `Lₙ` of the Lazard ring. -/
theorem mvPolynomialEquiv_mem_grading_iff {p : MvPolynomial ℕ+ ℤ} {n : ℕ} :
    mvPolynomialEquiv p ∈ grading n ↔ p.IsWeightedHomogeneous (fun k : ℕ+ ↦ 2 * (k : ℕ)) n := by
  set w : ℕ+ → ℕ := fun k ↦ 2 * (k : ℕ)
  -- Evaluation at the generators is a graded homomorphism.
  have hmem {m : ℕ} {q : MvPolynomial ℕ+ ℤ} (hq : q.IsWeightedHomogeneous w m) :
      mvPolynomialEquiv q ∈ grading m :=
    hq.aeval_mem fun k ↦ generator_mem_grading k
  refine ⟨fun hp ↦ ?_, hmem⟩
  let φ : MvPolynomial.weightedHomogeneousSubmodule ℤ w →+*ᵍ grading :=
    { toRingHom := mvPolynomialEquiv.toRingHom
      map_mem := fun hq ↦ hmem hq }
  -- `φ` is `mvPolynomialEquiv` as a graded ring homomorphism, so injectivity reflects
  -- homogeneity; `φ p` unfolds to `mvPolynomialEquiv p` by construction of `φ`.
  exact (MvPolynomial.mem_weightedHomogeneousSubmodule ℤ w n p).1
    ((Graded.map_mem_iff_of_injective φ mvPolynomialEquiv.injective).1 hp)

/-- `TauCeti.LazardRing.mvPolynomialEquiv` carries the ideal of variables onto the augmentation
ideal. -/
theorem mvPolynomialEquiv_mem_augmentationIdeal_iff {p : MvPolynomial ℕ+ ℤ} :
    mvPolynomialEquiv p ∈ augmentationIdeal ↔ p ∈ MvPolynomial.idealOfVars ℕ+ ℤ := by
  rw [mem_augmentationIdeal, augmentation_mvPolynomialEquiv, ← RingHom.mem_ker,
    MvPolynomial.ker_constantCoeff]

/-- `TauCeti.LazardRing.mvPolynomialEquiv` carries the `k`-th power of the ideal of variables onto
the `k`-th power of the augmentation ideal. -/
@[simp]
theorem mvPolynomialEquiv_mem_pow_augmentationIdeal_iff {p : MvPolynomial ℕ+ ℤ} {k : ℕ} :
    mvPolynomialEquiv p ∈ augmentationIdeal ^ k ↔ p ∈ MvPolynomial.idealOfVars ℕ+ ℤ ^ k := by
  have hcomap : augmentationIdeal.comap mvPolynomialEquiv.toRingEquiv =
      MvPolynomial.idealOfVars ℕ+ ℤ :=
    Ideal.ext fun _ ↦ mvPolynomialEquiv_mem_augmentationIdeal_iff
  rw [← AlgEquiv.coe_toRingEquiv, ← Ideal.mem_comap (f := mvPolynomialEquiv.toRingEquiv),
    ← Ideal.map_symm, Ideal.map_pow, Ideal.map_symm, hcomap]

/-- Any homogeneous element `z ∈ Lₘ` in the square of the augmentation ideal involves only
variables `X k` with `2k < m` under `mvPolynomialEquiv.symm`. -/
theorem two_mul_lt_of_mem_vars_mvPolynomialEquiv_symm {m : ℕ} {z : LazardRing}
    (hz : z ∈ grading m) (hz2 : z ∈ augmentationIdeal ^ 2) {k : ℕ+}
    (hk : k ∈ (mvPolynomialEquiv.symm z).vars) : 2 * (k : ℕ) < m := by
  have hhom : (mvPolynomialEquiv.symm z).IsWeightedHomogeneous (fun j : ℕ+ ↦ 2 * (j : ℕ)) m := by
    rwa [← mvPolynomialEquiv_mem_grading_iff, AlgEquiv.apply_symm_apply]
  have hdeg : mvPolynomialEquiv.symm z ∈ MvPolynomial.idealOfVars ℕ+ ℤ ^ 2 := by
    rwa [← mvPolynomialEquiv_mem_pow_augmentationIdeal_iff, AlgEquiv.apply_symm_apply]
  exact hhom.apply_lt_of_mem_sq_idealOfVars (fun j ↦ Nat.mul_pos Nat.zero_lt_two j.pos) hdeg hk

/-- **Triangularity of homogeneous lifts of `c • xₙ`.** If `y ∈ L₂ₙ` satisfies
`y ≡ c • xₙ (mod I²)`, then `mvPolynomialEquiv.symm y - c • X n` involves only variables `X k` with
`k < n`. -/
theorem lt_of_mem_vars_mvPolynomialEquiv_symm_sub_smul_X {n : ℕ+} {y : LazardRing} {c : ℤ}
    (hy : y ∈ grading (2 * (n : ℕ))) (hyc : y - c • generator n ∈ augmentationIdeal ^ 2)
    {k : ℕ+} (hk : k ∈ (mvPolynomialEquiv.symm y - c • MvPolynomial.X n).vars) : k < n := by
  have hsymm : mvPolynomialEquiv.symm (y - c • generator n) =
      mvPolynomialEquiv.symm y - c • MvPolynomial.X n := by simp
  have hlt := two_mul_lt_of_mem_vars_mvPolynomialEquiv_symm
    (sub_mem hy (zsmul_mem (generator_mem_grading n) c)) hyc (hsymm ▸ hk)
  exact (PNat.coe_lt_coe k n).1 (Nat.lt_of_mul_lt_mul_left hlt)

/-- Ring homomorphisms out of the Lazard ring lift along surjective ring homomorphisms: every
`g : L →+* S` factors as `f.comp g'` through any surjection `f : R →+* S`. -/
theorem exists_comp_eq_of_surjective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Surjective f) (g : LazardRing →+* S) :
    ∃ g' : LazardRing →+* R, f.comp g' = g := by
  obtain ⟨g', hg'⟩ := MvPolynomial.exists_comp_eq_of_surjective (f := f.toIntAlgHom) hf
    (g.toIntAlgHom.comp mvPolynomialEquiv.toAlgHom)
  refine ⟨g'.toRingHom.comp mvPolynomialEquiv.symm.toRingEquiv.toRingHom, RingHom.ext fun x ↦ ?_⟩
  simpa using DFunLike.congr_fun hg' (mvPolynomialEquiv.symm x)

end TauCeti.LazardRing

namespace FormalGroup

open TauCeti

/-- **Commutative formal group laws lift along surjections**: if `f : R →+* S` is surjective, every
commutative formal group law over `S` is the base change along `f` of a commutative formal group law
over `R`. -/
theorem exists_map_eq_of_surjective {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup S)
    [F.IsComm] {f : R →+* S} (hf : Function.Surjective f) :
    ∃ G : FormalGroup R, G.IsComm ∧ G.map f = F := by
  obtain ⟨g, hg⟩ := LazardRing.exists_comp_eq_of_surjective hf (LazardRing.lift ⟨F, ‹_›⟩)
  exact ⟨LazardRing.formalGroup.map g, inferInstance, by
    rw [map_comp, hg, LazardRing.map_lift]⟩

end FormalGroup
