/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Distribution.Star
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Convergence of noncommutative distributions

Convergence in moments tests every ordered word, including the empty word. Convergence in
star moments additionally tests adjoints. The approximating families may lie in different
algebras, as in matrix models with increasing dimension; only the scalar ring and the generator
labels are fixed. No topology on the algebras, positivity, trace, or normalization is required.

Word tests are equivalent to testing all noncommutative polynomials (respectively star
polynomials). Consequently convergence is preserved by fixed polynomial substitutions and by
relabeling, including restriction to a subfamily. The limiting distribution is unique, though
the realizing family need not be. For selfadjoint families moment and star-moment convergence
agree.

These notions concern moments, not weak convergence of measures. In particular they do not
assert convergence in operator norm or the existence of a bounded realization of a limit.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 4 and 8.

The polynomial test criterion uses Mathlib's `FreeAlgebra.basisFreeMonoid`.
-/

public section

open Filter Topology

namespace TauCeti

variable {R S T ι κ : Type*} {A : T → Type*} {B C : Type*}
  [CommSemiring R] [TopologicalSpace R]
  [∀ t, Semiring (A t)] [∀ t, Algebra R (A t)]
  [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
  {φ : (t : T) → A t →ₗ[R] R} {a : (t : T) → ι → A t} {l : Filter T}
  {ψ : B →ₗ[R] R} {b : ι → B} {χ : C →ₗ[R] R} {c : ι → C}

/-- Convergence in moments of algebraic families: every ordered word moment converges,
including the empty word. The ambient algebras may depend on the approximation parameter. -/
def TendstoInMoments (φ : (t : T) → A t →ₗ[R] R) (a : (t : T) → ι → A t)
    (l : Filter T) (ψ : B →ₗ[R] R) (b : ι → B) : Prop :=
  ∀ w : List ι, Tendsto (fun t => φ t (w.map (a t)).prod) l (𝓝 (ψ (w.map b).prod))

/-- The word-moment criterion includes the empty word, so it also tests normalization. -/
theorem tendstoInMoments_iff : TendstoInMoments φ a l ψ b ↔
    ∀ w : List ι, Tendsto (fun t => φ t (w.map (a t)).prod) l (𝓝 (ψ (w.map b).prod)) :=
  Iff.rfl

/-- Replacing the limiting family by one with the same distribution preserves convergence. -/
theorem TendstoInMoments.congr_limit (h : TendstoInMoments φ a l ψ b)
    (e : jointDistribution ψ b = jointDistribution χ c) : TendstoInMoments φ a l χ c := by
  rw [tendstoInMoments_iff] at h ⊢
  intro w
  rw [← jointDistribution_eq_iff.1 e w]
  exact h w

/-- Restricting the approximation filter preserves moment convergence. -/
theorem TendstoInMoments.mono_left (h : TendstoInMoments φ a l ψ b)
    {l' : Filter T} (hl : l' ≤ l) : TendstoInMoments φ a l' ψ b := by
  rw [tendstoInMoments_iff] at h ⊢
  exact fun w => (h w).mono_left hl

/-- Reindexing along a convergent map preserves moment convergence. -/
theorem TendstoInMoments.comp_tendsto (h : TendstoInMoments φ a l ψ b)
    {f : S → T} {l' : Filter S} (hf : Tendsto f l' l) :
    TendstoInMoments (fun s => φ (f s)) (fun s => a (f s)) l' ψ b := by
  rw [tendstoInMoments_iff] at h ⊢
  exact fun w => (h w).comp hf

/-- Eventual equality of each word moment preserves moment convergence, even between
families in different algebras. The eventual set may depend on the word. -/
theorem TendstoInMoments.congr' (h : TendstoInMoments φ a l ψ b)
    {D : T → Type*} [∀ t, Semiring (D t)] [∀ t, Algebra R (D t)]
    {φ' : (t : T) → D t →ₗ[R] R} {a' : (t : T) → ι → D t}
    (e : ∀ w : List ι, ∀ᶠ t in l, φ t (w.map (a t)).prod = φ' t (w.map (a' t)).prod) :
    TendstoInMoments φ' a' l ψ b := by
  rw [tendstoInMoments_iff] at h ⊢
  exact fun w => (h w).congr' (e w)

/-- Moment convergence implies convergence of the expectation of every noncommutative
polynomial, not just monomials. -/
theorem TendstoInMoments.tendsto_jointDistribution [IsTopologicalSemiring R]
    (h : TendstoInMoments φ a l ψ b) (p : FreeAlgebra R ι) :
    Tendsto (fun t => jointDistribution (φ t) (a t) p) l (𝓝 (jointDistribution ψ b p)) := by
  classical
  rw [← (FreeAlgebra.basisFreeMonoid R ι).linearCombination_repr p,
    Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply tendsto_finsetSum
  intro w _
  exact tendsto_const_nhds.mul (by
    simpa only [jointDistribution_basisFreeMonoid] using h w.toList)

/-- Testing all polynomials is equivalent to testing all word moments. -/
theorem tendstoInMoments_iff_forall_tendsto_jointDistribution [IsTopologicalSemiring R] :
    TendstoInMoments φ a l ψ b ↔
    ∀ p : FreeAlgebra R ι,
      Tendsto (fun t => jointDistribution (φ t) (a t) p) l (𝓝 (jointDistribution ψ b p)) := by
  refine ⟨fun h => h.tendsto_jointDistribution, fun h w => ?_⟩
  simpa only [jointDistribution_list_prod] using h (w.map (FreeAlgebra.ι R)).prod

/-- Fixed polynomial substitutions preserve convergence in moments. -/
theorem TendstoInMoments.subst [IsTopologicalSemiring R] (h : TendstoInMoments φ a l ψ b)
    (p : κ → FreeAlgebra R ι) :
    TendstoInMoments φ (fun t j => FreeAlgebra.lift R (a t) (p j)) l
      ψ (fun j => FreeAlgebra.lift R b (p j)) := by
  apply tendstoInMoments_iff_forall_tendsto_jointDistribution.2
  intro q
  simpa only [jointDistribution_subst, jointDistribution_apply] using
    h.tendsto_jointDistribution (FreeAlgebra.lift R p q)

/-- Relabeling and restriction to a subfamily preserve moment convergence. -/
theorem TendstoInMoments.comp (h : TendstoInMoments φ a l ψ b) (r : κ → ι) :
    TendstoInMoments φ (fun t => a t ∘ r) l ψ (b ∘ r) := by
  intro w
  simpa only [List.map_map, Function.comp_def] using h (w.map r)

/-- A surjective relabeling loses no information about moment convergence. -/
theorem tendstoInMoments_comp_iff {r : κ → ι} (hr : Function.Surjective r) :
    TendstoInMoments φ (fun t => a t ∘ r) l ψ (b ∘ r) ↔ TendstoInMoments φ a l ψ b := by
  classical
  refine ⟨fun h => ?_, fun h => h.comp r⟩
  simpa only [Function.comp_def, Function.surjInv_eq hr] using h.comp (Function.surjInv hr)

/-- A fixed family converges in moments to itself. -/
theorem tendstoInMoments_const (l : Filter T) (ψ : B →ₗ[R] R) (b : ι → B) :
    TendstoInMoments (fun _ : T => ψ) (fun _ => b) l ψ b :=
  fun _ => tendsto_const_nhds

/-- A moment limit determines a unique joint distribution, not a unique realization. -/
theorem TendstoInMoments.jointDistribution_eq [T2Space R] [l.NeBot]
    (h : TendstoInMoments φ a l ψ b) (h' : TendstoInMoments φ a l χ c) :
    jointDistribution ψ b = jointDistribution χ c :=
  jointDistribution_eq_iff.2 fun w => tendsto_nhds_unique (h w) (h' w)

section Star

variable [∀ t, StarRing (A t)] [StarRing B] [StarRing C]

/-- Convergence in star moments tests every ordered word in variables and their adjoints,
including the empty word. The realizing star algebras may vary with the parameter. -/
def TendstoInStarMoments (φ : (t : T) → A t →ₗ[R] R) (a : (t : T) → ι → A t)
    (l : Filter T) (ψ : B →ₗ[R] R) (b : ι → B) : Prop :=
  TendstoInMoments φ (fun t => StarPolynomial.withStar (a t)) l ψ (StarPolynomial.withStar b)

/-- Star-moment convergence is moment convergence of the variables together with their
adjoints, with the two letters for each variable kept distinct. -/
theorem tendstoInStarMoments_iff : TendstoInStarMoments φ a l ψ b ↔
    TendstoInMoments φ (fun t => StarPolynomial.withStar (a t)) l ψ
      (StarPolynomial.withStar b) := Iff.rfl

/-- Replacing the limiting family by one with the same star distribution preserves
star-moment convergence. -/
theorem TendstoInStarMoments.congr_limit [StarRing R] [StarModule R B] [StarModule R C]
    (h : TendstoInStarMoments φ a l ψ b)
    (e : starDistribution ψ b = starDistribution χ c) : TendstoInStarMoments φ a l χ c := by
  rw [tendstoInStarMoments_iff] at h ⊢
  exact h.congr_limit (starDistribution_eq_iff_jointDistribution_withStar_eq.1 e)

/-- Restricting the approximation filter preserves star-moment convergence. -/
theorem TendstoInStarMoments.mono_left (h : TendstoInStarMoments φ a l ψ b)
    {l' : Filter T} (hl : l' ≤ l) : TendstoInStarMoments φ a l' ψ b := by
  rw [tendstoInStarMoments_iff] at h ⊢
  exact h.mono_left hl

/-- Reindexing along a convergent map preserves star-moment convergence. -/
theorem TendstoInStarMoments.comp_tendsto (h : TendstoInStarMoments φ a l ψ b)
    {f : S → T} {l' : Filter S} (hf : Tendsto f l' l) :
    TendstoInStarMoments (fun s => φ (f s)) (fun s => a (f s)) l' ψ b := by
  rw [tendstoInStarMoments_iff] at h ⊢
  exact h.comp_tendsto hf

/-- Eventual equality of each word moment in variables and adjoints preserves star-moment
convergence, even between different algebras. The eventual set may depend on the word. -/
theorem TendstoInStarMoments.congr' (h : TendstoInStarMoments φ a l ψ b)
    {D : T → Type*} [∀ t, Semiring (D t)] [∀ t, Algebra R (D t)] [∀ t, StarRing (D t)]
    {φ' : (t : T) → D t →ₗ[R] R} {a' : (t : T) → ι → D t}
    (e : ∀ w : List (ι × Bool), ∀ᶠ t in l,
      φ t (w.map (StarPolynomial.withStar (a t))).prod =
        φ' t (w.map (StarPolynomial.withStar (a' t))).prod) :
    TendstoInStarMoments φ' a' l ψ b := by
  rw [tendstoInStarMoments_iff] at h ⊢
  exact h.congr' e

/-- Star-moment convergence implies convergence of every star-polynomial expectation. -/
theorem TendstoInStarMoments.tendsto_starDistribution [IsTopologicalSemiring R] [StarRing R]
    [∀ t, StarModule R (A t)] [StarModule R B] (h : TendstoInStarMoments φ a l ψ b)
    (p : StarPolynomial R ι) :
    Tendsto (fun t => starDistribution (φ t) (a t) p) l (𝓝 (starDistribution ψ b p)) := by
  simpa only [starDistribution_apply, StarPolynomial.lift_apply, jointDistribution_apply] using
    (tendstoInStarMoments_iff.1 h).tendsto_jointDistribution (StarPolynomial.toFreeAlgebra R ι p)

/-- Testing all star polynomials is equivalent to testing words in variables and adjoints. -/
theorem tendstoInStarMoments_iff_forall_tendsto_starDistribution
    [IsTopologicalSemiring R] [StarRing R] [∀ t, StarModule R (A t)] [StarModule R B] :
    TendstoInStarMoments φ a l ψ b ↔
    ∀ p : StarPolynomial R ι,
      Tendsto (fun t => starDistribution (φ t) (a t) p) l (𝓝 (starDistribution ψ b p)) := by
  refine ⟨fun h => h.tendsto_starDistribution, fun h => ?_⟩
  apply tendstoInMoments_iff_forall_tendsto_jointDistribution.2
  intro q
  simpa only [starDistribution_apply, StarPolynomial.lift_apply,
    AlgEquiv.apply_symm_apply, jointDistribution_apply] using
    h ((StarPolynomial.toFreeAlgebra R ι).symm q)

/-- Fixed star-polynomial substitutions preserve convergence in star moments. -/
theorem TendstoInStarMoments.subst [IsTopologicalSemiring R] [StarRing R]
    [∀ t, StarModule R (A t)] [StarModule R B] (h : TendstoInStarMoments φ a l ψ b)
    (p : κ → StarPolynomial R ι) :
    TendstoInStarMoments φ (fun t j => StarPolynomial.lift (a t) (p j)) l
      ψ (fun j => StarPolynomial.lift b (p j)) := by
  apply tendstoInStarMoments_iff_forall_tendsto_starDistribution.2
  intro q
  simpa only [starDistribution_subst, starDistribution_apply] using
    h.tendsto_starDistribution (StarPolynomial.lift p q)

/-- Relabeling and restriction to a subfamily preserve star-moment convergence. -/
theorem TendstoInStarMoments.comp (h : TendstoInStarMoments φ a l ψ b) (r : κ → ι) :
    TendstoInStarMoments φ (fun t => a t ∘ r) l ψ (b ∘ r) := by
  rw [tendstoInStarMoments_iff] at h ⊢
  simpa only [StarPolynomial.withStar_comp] using h.comp (Prod.map r id)

/-- A surjective relabeling loses no information about star-moment convergence. -/
theorem tendstoInStarMoments_comp_iff {r : κ → ι} (hr : Function.Surjective r) :
    TendstoInStarMoments φ (fun t => a t ∘ r) l ψ (b ∘ r) ↔
      TendstoInStarMoments φ a l ψ b := by
  classical
  refine ⟨fun h => ?_, fun h => h.comp r⟩
  simpa only [Function.comp_def, Function.surjInv_eq hr] using h.comp (Function.surjInv hr)

/-- Star-moment convergence implies ordinary moment convergence. -/
theorem TendstoInStarMoments.tendstoInMoments (h : TendstoInStarMoments φ a l ψ b) :
    TendstoInMoments φ a l ψ b := by
  simpa only [Function.comp_def, StarPolynomial.withStar_mk_false] using
    (tendstoInStarMoments_iff.1 h).comp (fun i => (i, false))

/-- For selfadjoint families, moment convergence and star-moment convergence coincide. -/
theorem tendstoInStarMoments_iff_tendstoInMoments_of_isSelfAdjoint
    (ha : ∀ t i, IsSelfAdjoint (a t i)) (hb : ∀ i, IsSelfAdjoint (b i)) :
    TendstoInStarMoments φ a l ψ b ↔ TendstoInMoments φ a l ψ b := by
  refine ⟨fun h => h.tendstoInMoments, fun h => ?_⟩
  rw [tendstoInStarMoments_iff]
  simpa only [StarPolynomial.withStar_eq_comp_fst (ha _),
    StarPolynomial.withStar_eq_comp_fst hb] using h.comp (Prod.fst : ι × Bool → ι)

/-- A fixed star-algebraic family converges in star moments to itself. -/
theorem tendstoInStarMoments_const (l : Filter T) (ψ : B →ₗ[R] R) (b : ι → B) :
    TendstoInStarMoments (fun _ : T => ψ) (fun _ => b) l ψ b :=
  tendstoInMoments_const l ψ (StarPolynomial.withStar b)

/-- A star-moment limit determines a unique star distribution. -/
theorem TendstoInStarMoments.starDistribution_eq [T2Space R] [l.NeBot] [StarRing R]
    [StarModule R B] [StarModule R C]
    (h : TendstoInStarMoments φ a l ψ b) (h' : TendstoInStarMoments φ a l χ c) :
    starDistribution ψ b = starDistribution χ c := by
  rw [starDistribution_eq_iff_jointDistribution_withStar_eq]
  exact (tendstoInStarMoments_iff.1 h).jointDistribution_eq (tendstoInStarMoments_iff.1 h')

end Star

end TauCeti
