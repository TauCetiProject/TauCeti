/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Nondegenerate
public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Toral
import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Plane
import TauCeti.Geometry.Symplectic.Plane
import TauCeti.Geometry.Symplectic.Restrict
import TauCeti.Geometry.Symplectic.Spectrum

/-!
# Williamson's classification of nondegenerate families: the elliptic–hyperbolic case

Let `(V, ω)` be a finite-dimensional real symplectic vector space of dimension `2n`. A family `Q`
of quadratic forms on `V` is nondegenerate
(`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily`) when the Hamiltonian endomorphisms
`A_{Q i}` generate a Cartan subalgebra `𝔥` of `sp(V, ω)`. Williamson's classification puts such a
family, up to its span, into a normal form made of
elliptic, hyperbolic and focus-focus blocks in a suitable Darboux basis. This file proves the
classification for the Cartan subalgebras **without focus-focus blocks**, those containing an
element `A_P` whose square has `n` distinct nonzero real eigenvalues:

`∃ P ∈ span Q, A_P² has n distinct nonzero real eigenvalues  ↔  span Q = span (B₁, …, Bₙ)`

where, for some Darboux basis `(q₁, p₁, …, qₙ, pₙ)` and some set `t` of planes, `Bₖ` is the
elliptic block `Iₖ = (xₖ² + yₖ²) / 2` for `k ∈ t` and the hyperbolic block `Hₖ = xₖ yₖ` for
`k ∉ t` (`TauCeti.SymplecticForm.ellipticHyperbolic`); this is
`IsNondegenerateQuadraticFamily.exists_mem_span_card_mul_two_eq_finrank_iff` in the namespace
`TauCeti.SymplecticForm`.
This contains the purely hyperbolic case, a form whose Hamiltonian endomorphism has `2n` distinct
real eigenvalues `±aₖ`, and mixes it with elliptic planes, on which `A_P` has the eigenvalues
`±i cₖ`. The negative eigenvalues `-cₖ²` of `A_P²` give the elliptic planes and its positive
eigenvalues `aₖ²` the hyperbolic ones.

The proof has three steps. Let `A = A_P` and let `s` be the set of the `n` eigenvalues of `A²`.

* **The generalized eigenspaces of `A²` are planes.** For `μ ∈ s`, the vectors `G_μ` killed by a
  power of `A² - μ` form a symplectic subspace, since `X² - μ` is an even polynomial
  (`TauCeti.SymplecticForm.isSymplectic_maxGenEigenspace_aeval`), and `G_μ` and `G_ν` are
  `ω`-orthogonal for `μ ≠ ν`. Each `G_μ` contains an eigenvector of `A²`, so a pair `(x_μ, y_μ)`
  with `ω(x_μ, y_μ) = 1`. These `2n` vectors satisfy the Darboux relations, so they form a Darboux
  basis of `V`, and expanding a vector of `G_μ` in it shows that `G_μ = span(x_μ, y_μ)` is a plane.
* **Normal pairs.** On the plane `G_μ`, preserved by `A`, the square of `A` is a homothety
  (`TauCeti.SymplecticForm.exists_mul_self_eq_smul_one`), so `A² = μ` there. For `μ = a² > 0`
  this gives a hyperbolic pair `(q, p)` in `G_μ`, with `A q = a q` and `A p = -a p`; for
  `μ = -c² < 0` an elliptic pair, with `A q = -c p` and `A p = c q`. Assembling the pairs gives a
  Darboux basis in which `P = ∑ₖ cₖ Bₖ`, the squares `-cₖ²` (elliptic) and `cₖ²` (hyperbolic)
  being the elements of `s`
  (`TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_ellipticHyperbolic`).
* **Equality of spans.** The forms `Q i` Poisson-commute with `P`, since `𝔥` is abelian, and the
  coefficients `cₖ` are nonzero with squares distinct between blocks of the same type, so every
  `Q i` is a combination of the blocks
  (`IsDarbouxBasis.mem_span_ellipticHyperbolic_of_quadraticPoissonBracket_eq_zero` in the
  namespace `TauCeti.SymplecticForm`). The blocks form a nondegenerate family, which is maximal
  among Poisson-commuting families
  (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.span_eq_of_span_le`), so the two spans
  are equal.

Conversely, for the form `∑ₖ (k + 1) Bₖ` the square of the Hamiltonian endomorphism has the `n`
distinct eigenvalues `∓(k + 1)²`, with eigenvectors `qₖ`.

The focus-focus blocks, on which `A_P` has four eigenvalues `±a ± i b`, are not treated here.

## Main results

All declarations are in the namespace `TauCeti.SymplecticForm`.

* `exists_isDarbouxBasis_eq_sum_smul_ellipticHyperbolic`: a quadratic form `P` such that `A_P²`
  has `dim V / 2` distinct nonzero real eigenvalues is `∑ₖ cₖ Bₖ` in some Darboux basis.
* `IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_ellipticHyperbolic`: a
  nondegenerate family whose span contains such a form spans the elliptic–hyperbolic blocks of a
  Darboux basis.
* `IsNondegenerateQuadraticFamily.exists_mem_span_card_mul_two_eq_finrank_iff`: this
  characterizes the nondegenerate families of elliptic–hyperbolic type.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
-/

public section

open Module Polynomial

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V}

variable {A : Module.End ℝ V}

/-- The polynomial `X² - μ` is even. -/
private theorem comp_neg_X_sq_sub_C (μ : ℝ) : (X ^ 2 - C μ : ℝ[X]).comp (-X) = X ^ 2 - C μ := by
  simp [sub_comp]

/-- For `A ∈ sp(V, ω)`, the vectors killed by a power of `A² - μ` form a symplectic subspace. -/
private theorem isSymplectic_maxGenEigenspace_sq_sub [FiniteDimensional ℝ V]
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) (μ : ℝ) :
    ω.IsSymplectic ((aeval A (X ^ 2 - C μ)).maxGenEigenspace 0) :=
  ω.isSymplectic_maxGenEigenspace_aeval hA (comp_neg_X_sq_sub_C μ)

/-- For `A ∈ sp(V, ω)` and `μ ≠ ν`, `ω` pairs the vectors killed by a power of `A² - μ` trivially
with those killed by a power of `A² - ν`. -/
private theorem apply_eq_zero_of_mem_maxGenEigenspace_sq_sub
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {μ ν : ℝ} (hμν : μ ≠ ν) {v w : V}
    (hv : v ∈ (aeval A (X ^ 2 - C μ)).maxGenEigenspace 0)
    (hw : w ∈ (aeval A (X ^ 2 - C ν)).maxGenEigenspace 0) : ω v w = 0 := by
  refine ((LinearMap.mem_skewAdjointSubmodule A).1 hA).apply_eq_zero_of_mem_maxGenEigenspace_aeval
    ?_ hv hw
  rw [comp_neg_X_sq_sub_C]
  have h := (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hμν).isUnit).map
    (compRingHom (X ^ 2 : ℝ[X]))
  simpa using h

/-- An eigenvector of `A²` for `μ` is killed by `A² - μ`. -/
private theorem mem_maxGenEigenspace_sq_sub {μ : ℝ} {v : V} (hv : A (A v) = μ • v) :
    v ∈ (aeval A (X ^ 2 - C μ)).maxGenEigenspace 0 :=
  (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by simp [sq, hv]⟩

/-- For `A ∈ sp(V, ω)`, the vectors killed by powers of `A² - μ` for the distinct `μ ∈ s`, indexed
by `Fin s.card`, are pairwise `ω`-orthogonal. -/
private theorem pairwise_apply_eq_zero_of_mem_maxGenEigenspace_sq_sub
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) (s : Finset ℝ) :
    Pairwise fun k l : Fin s.card ↦
      ∀ v ∈ (aeval A (X ^ 2 - C (s.equivFin.symm k : ℝ))).maxGenEigenspace 0,
        ∀ w ∈ (aeval A (X ^ 2 - C (s.equivFin.symm l : ℝ))).maxGenEigenspace 0, ω v w = 0 :=
  fun _ _ hkl _ hv _ hw ↦ apply_eq_zero_of_mem_maxGenEigenspace_sq_sub hA
    (fun h ↦ hkl (s.equivFin.symm.injective (Subtype.ext h))) hv hw

variable [FiniteDimensional ℝ V]

/-- **The generalized eigenspaces of `A²` are planes.** If `A ∈ sp(V, ω)` and `A²` has
`dim V / 2` distinct eigenvalues `μ ∈ s`, then for each of them the vectors killed by a power of
`A² - μ` form a plane. -/
private theorem finrank_maxGenEigenspace_sq_sub
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {s : Finset ℝ}
    (hs : s.card * 2 = finrank ℝ V) (hAs : ∀ μ ∈ s, (A ^ 2).HasEigenvalue μ) {μ : ℝ}
    (hμ : μ ∈ s) : finrank ℝ ((aeval A (X ^ 2 - C μ)).maxGenEigenspace 0) = 2 := by
  set G : ℝ → Submodule ℝ V := fun ν ↦ (aeval A (X ^ 2 - C ν)).maxGenEigenspace 0
  -- In each `G ν`, a nonzero eigenvector `x ν` of `A²` and a partner `y ν` with
  -- `ω(x ν, y ν) = 1`.
  have hx (ν : s) : ∃ x ∈ G ν, x ≠ 0 := by
    obtain ⟨x, hx⟩ := (hAs ν ν.property).exists_hasEigenvector
    refine ⟨x, mem_maxGenEigenspace_sq_sub ?_, hx.2⟩
    simpa [sq] using hx.apply_eq_smul
  choose x hxG hx0 using hx
  have hy (ν : s) : ∃ y ∈ G ν, ω (x ν) y = 1 := by
    have hL := isSymplectic_maxGenEigenspace_sq_sub hA (ν : ℝ)
    obtain ⟨y, hy⟩ := (ω.restrict (G ν) hL.nondegenerate_restrict).exists_apply_eq_one
      (x := ⟨x ν, hxG ν⟩) (by simpa using hx0 ν)
    exact ⟨y, y.property, by simpa using hy⟩
  choose y hyG hxy using hy
  -- These vectors, indexed by `Fin s.card`, form a Darboux basis.
  set e : Fin s.card ≃ s := s.equivFin.symm
  have horth : Pairwise fun k l ↦ ∀ v ∈ G (e k), ∀ w ∈ G (e l), ω v w = 0 :=
    pairwise_apply_eq_zero_of_mem_maxGenEigenspace_sq_sub hA s
  obtain ⟨b, hb, hbx, hby⟩ := exists_isDarbouxBasis_of_forall_mem hs.symm horth
    (fun k ↦ hxG (e k)) (fun k ↦ hyG (e k)) fun k ↦ hxy (e k)
  -- A vector of `G μ` has no coordinates outside the plane `k₀` of `μ`.
  set k₀ := e.symm ⟨μ, hμ⟩
  have hle : G μ ≤ Submodule.span ℝ (Set.range fun j : Fin 2 ↦ b (k₀, j)) := by
    intro w hw
    have hw' : w ∈ G (e k₀) := by simpa [k₀] using hw
    have hrepr (k : Fin s.card) (hk : k ≠ k₀) (j : Fin 2) : b.repr w (k, j) = 0 := by
      obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · rw [← neg_eq_zero, ← hb.apply_snd, hby]
        exact horth hk _ (hyG _) _ hw'
      · rw [← hb.apply_fst, hbx]
        exact horth hk _ (hxG _) _ hw'
    rw [← b.sum_repr w, Fintype.sum_prod_type,
      Finset.sum_eq_single k₀ (fun k _ hk ↦ by simp [hrepr k hk]) (by simp)]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  -- `G μ` is a nonzero symplectic subspace of dimension at most two, hence a plane.
  have hle2 : finrank ℝ (G μ) ≤ 2 :=
    (Submodule.finrank_mono hle).trans ((finrank_range_le_card _).trans (by simp))
  obtain ⟨r, hr⟩ := (ω.restrict (G μ)
    (isSymplectic_maxGenEigenspace_sq_sub hA μ).nondegenerate_restrict).even_finrank
  have hx' : x ⟨μ, hμ⟩ ∈ G μ := hxG ⟨μ, hμ⟩
  have hpos : finrank ℝ (G μ) ≠ 0 := fun h0 ↦
    hx0 _ ((Submodule.mem_bot ℝ).1 (Submodule.finrank_eq_zero.1 h0 ▸ hx'))
  -- `omega` needs the goal stated with the same atom `G μ` as the hypotheses.
  change finrank ℝ (G μ) = 2
  omega

/-- On the plane of vectors killed by a power of `A² - μ`, the square of `A` is `μ`. -/
private theorem apply_apply_eq_of_mem_maxGenEigenspace_sq_sub
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {s : Finset ℝ}
    (hs : s.card * 2 = finrank ℝ V) (hAs : ∀ μ ∈ s, (A ^ 2).HasEigenvalue μ) {μ : ℝ}
    (hμ : μ ∈ s) :
    A.restrict (End.mapsTo_maxGenEigenspace_aeval_of_comm (Commute.refl A) (X ^ 2 - C μ) 0) *
        A.restrict (End.mapsTo_maxGenEigenspace_aeval_of_comm (Commute.refl A) (X ^ 2 - C μ) 0) =
      μ • 1 := by
  set L := (aeval A (X ^ 2 - C μ)).maxGenEigenspace 0
  have hL := isSymplectic_maxGenEigenspace_sq_sub hA μ
  obtain ⟨κ, hκ⟩ := exists_mul_self_eq_smul_one (ω := ω.restrict L hL.nondegenerate_restrict)
    (finrank_maxGenEigenspace_sq_sub hA hs hAs hμ)
    ⟨_, restrict_mem_skewAdjointLieSubalgebra hA hL.nondegenerate_restrict
      (End.mapsTo_maxGenEigenspace_aeval_of_comm (Commute.refl A) _ 0)⟩
  -- An eigenvector of `A²` for `μ` lies in `L`, so `κ = μ`.
  obtain ⟨x, hx⟩ := (hAs μ hμ).exists_hasEigenvector
  have hxμ : A (A x) = μ • x := by simpa [sq] using hx.apply_eq_smul
  have hxL : x ∈ L := mem_maxGenEigenspace_sq_sub hxμ
  -- The restriction of `A` evaluates on `L` as `A` does, definitionally.
  have h : A (A x) = κ • x := congrArg Subtype.val (LinearMap.congr_fun hκ ⟨x, hxL⟩)
  rw [hxμ] at h
  obtain rfl : κ = μ := (smul_left_injective ℝ hx.2 h).symm
  exact hκ

/-- **Normal pairs on the planes of `A²`.** If `A ∈ sp(V, ω)` and `A²` has `dim V / 2` distinct
eigenvalues `ν ∈ s`, then for each nonzero `ν` the plane of vectors killed by a power of `A² - ν`
contains a pair `(q, p)` with `ω(q, p) = 1` on which `A` is elliptic, `A q = -c p` and
`A p = c q` with `ν = -c²`, when `ν < 0`, and hyperbolic, `A q = c q` and `A p = -c p` with
`ν = c²`, when `ν > 0`. -/
private theorem exists_pair_mem_maxGenEigenspace_sq_sub
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {s : Finset ℝ}
    (hs : s.card * 2 = finrank ℝ V) (hAs : ∀ μ ∈ s, (A ^ 2).HasEigenvalue μ) {ν : ℝ}
    (hν : ν ∈ s) (hν0 : ν ≠ 0) :
    ∃ q ∈ (aeval A (X ^ 2 - C ν)).maxGenEigenspace 0,
      ∃ p ∈ (aeval A (X ^ 2 - C ν)).maxGenEigenspace 0, ∃ c : ℝ, c ≠ 0 ∧ ω q p = 1 ∧
        (ν < 0 → -c ^ 2 = ν ∧ A q = -c • p ∧ A p = c • q) ∧
        (0 < ν → c ^ 2 = ν ∧ A q = c • q ∧ A p = -c • p) := by
  -- Work on the plane `L` with the restrictions `ω'` of `ω` and `A'` of `A`.
  set L := (aeval A (X ^ 2 - C ν)).maxGenEigenspace 0
  have hL := isSymplectic_maxGenEigenspace_sq_sub hA ν
  set ω' := ω.restrict L hL.nondegenerate_restrict
  set A' := A.restrict
    (End.mapsTo_maxGenEigenspace_aeval_of_comm (Commute.refl A) (X ^ 2 - C ν) 0)
  have hA' : A' ∈ skewAdjointLieSubalgebra ω'.toBilinForm :=
    restrict_mem_skewAdjointLieSubalgebra hA hL.nondegenerate_restrict _
  have hAA : A' * A' = ν • 1 := apply_apply_eq_of_mem_maxGenEigenspace_sq_sub hA hs hAs hν
  have hfin : finrank ℝ L = 2 := finrank_maxGenEigenspace_sq_sub hA hs hAs hν
  have : Nontrivial L := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfin]; norm_num)
  rcases lt_or_gt_of_ne hν0 with hneg | hpos
  · -- Elliptic plane: `ν = -c²`, with the sign of `c` that of `ω(A v, v)` for any `v ≠ 0`.
    obtain ⟨v, hv0⟩ := exists_ne (0 : L)
    have hv := apply_ne_zero_of_neg_of_mul_self_eq_smul_one (ω := ω') hfin hneg hAA hv0
    have hsqrt : 0 < √(-ν) := Real.sqrt_pos.2 (neg_pos.2 hneg)
    have hsqrt2 : √(-ν) ^ 2 = -ν := Real.sq_sqrt (neg_nonneg.2 hneg.le)
    obtain ⟨c, hsq, hc⟩ : ∃ c : ℝ, c ^ 2 = -ν ∧ 0 < c * ω' (A' v) v := by
      rcases lt_or_gt_of_ne hv with h | h
      · exact ⟨-√(-ν), by rw [neg_sq, hsqrt2], by nlinarith⟩
      · exact ⟨√(-ν), hsqrt2, by positivity⟩
    have hAAv : A' (A' v) = -(c ^ 2) • v := by
      simpa [hsq] using LinearMap.congr_fun hAA v
    obtain ⟨q, p, hqp, hAq, hAp, -⟩ := exists_apply_eq_one_apply_eq_neg_smul_apply_eq_smul hAAv hc
    exact ⟨q, q.property, p, p.property, c, fun h ↦ by simp [h] at hc, hqp,
      fun _ ↦ ⟨by rw [hsq, neg_neg], congrArg Subtype.val hAq, congrArg Subtype.val hAp⟩,
      fun h ↦ absurd h hneg.not_gt⟩
  · -- Hyperbolic plane: `ν = a²` with `a = √ν > 0`.
    have hsq : √ν ^ 2 = ν := Real.sq_sqrt hpos.le
    have ha : √ν ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    obtain ⟨q, p, hqp, hAq, hAp⟩ :=
      exists_apply_eq_one_apply_eq_smul_apply_eq_neg_smul hA' ha (by rw [hsq, hAA])
    exact ⟨q, q.property, p, p.property, √ν, ha, hqp, fun h ↦ absurd h hpos.not_gt,
      fun _ ↦ ⟨hsq, congrArg Subtype.val hAq, congrArg Subtype.val hAp⟩⟩

variable (ω) in
/-- **Williamson's normal form of a regular elliptic–hyperbolic quadratic Hamiltonian.** If the
square of the Hamiltonian endomorphism `A_P` of a quadratic form `P` has `dim V / 2` distinct
nonzero real eigenvalues, listed in a finite set `s`, then there are a Darboux basis
`(q₁, p₁, …, qₙ, pₙ)`, a set `t` of planes and nonzero reals `cₖ` with `P = ∑ₖ cₖ Bₖ`, where `Bₖ`
is the elliptic block `(xₖ² + yₖ²) / 2` for `k ∈ t` and the hyperbolic block `xₖ yₖ` for `k ∉ t`.
On the `k`-th plane `A_P²` is `-cₖ²` for `k ∈ t` and `cₖ²` for `k ∉ t`, and these values are the
elements of `s`, each taken once. -/
theorem exists_isDarbouxBasis_eq_sum_smul_ellipticHyperbolic {P : QuadraticForm ℝ V}
    {s : Finset ℝ} (hs : s.card * 2 = finrank ℝ V) (hs0 : (0 : ℝ) ∉ s)
    (hP : ∀ μ ∈ s, (ω.hamiltonianEnd P ^ 2).HasEigenvalue μ) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (t : Finset (Fin n)) (c : Fin n → ℝ),
      ω.IsDarbouxBasis b ∧ (∀ k, c k ≠ 0) ∧
      Function.Injective (fun k ↦ if k ∈ t then -c k ^ 2 else c k ^ 2) ∧
      Finset.univ.image (fun k ↦ if k ∈ t then -c k ^ 2 else c k ^ 2) = s ∧
      P = ∑ k, c k • ellipticHyperbolic b t k := by
  have hA := ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra P
  -- A normal pair `(q ν, p ν)` with coefficient `c ν` on the plane of each eigenvalue `ν` of
  -- `A_P²`, the planes indexed by `Fin s.card`; the pairs form a Darboux basis.
  choose q hqG p hpG c hc0 hqp hell hhyp using fun ν : s ↦
    exists_pair_mem_maxGenEigenspace_sq_sub hA hs hP ν.property fun h ↦ hs0 (h ▸ ν.property)
  set e : Fin s.card ≃ s := s.equivFin.symm
  obtain ⟨b, hb, hbq, hbp⟩ := exists_isDarbouxBasis_of_forall_mem hs.symm
    (pairwise_apply_eq_zero_of_mem_maxGenEigenspace_sq_sub hA s) (fun k ↦ hqG (e k))
    (fun k ↦ hpG (e k)) fun k ↦ hqp (e k)
  -- The elliptic planes are those of the negative eigenvalues.
  set t : Finset (Fin s.card) := Finset.univ.filter fun k ↦ (e k : ℝ) < 0
  have hmemt (k : Fin s.card) : k ∈ t ↔ (e k : ℝ) < 0 := by simp [t]
  have hnotmemt {k : Fin s.card} (hk : k ∉ t) : 0 < (e k : ℝ) :=
    lt_of_le_of_ne (not_lt.1 (mt (hmemt k).2 hk)) fun h ↦ hs0 (h ▸ (e k).property)
  have hμ (k : Fin s.card) : (if k ∈ t then -c (e k) ^ 2 else c (e k) ^ 2) = e k := by
    by_cases hk : k ∈ t
    · simpa only [hk, ↓reduceIte] using (hell (e k) ((hmemt k).1 hk)).1
    · simpa only [hk, ↓reduceIte] using (hhyp (e k) (hnotmemt hk)).1
  refine ⟨s.card, b, t, fun k ↦ c (e k), hb, fun k ↦ hc0 _, fun k l hkl ↦ ?_, ?_, ?_⟩
  · simp only [hμ] at hkl
    exact e.injective (Subtype.ext hkl)
  · ext ν
    simp only [hμ, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨by rintro ⟨k, rfl⟩; exact (e k).property, fun hν ↦ ⟨e.symm ⟨ν, hν⟩, by simp⟩⟩
  -- `A_P` and the Hamiltonian endomorphism of `∑ₖ cₖ Bₖ` agree on the basis.
  refine ω.hamiltonianEnd_injective (b.ext fun ⟨k, j⟩ ↦ ?_)
  obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
  · rw [hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_fst, hbq, hbp]
    by_cases hk : k ∈ t
    · simpa [hk] using (hell (e k) ((hmemt k).1 hk)).2.1
    · simpa [hk] using (hhyp (e k) (hnotmemt hk)).2.1
  · rw [hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_snd, hbq, hbp]
    by_cases hk : k ∈ t
    · simpa [hk] using (hell (e k) ((hmemt k).1 hk)).2.2
    · simpa [hk] using (hhyp (e k) (hnotmemt hk)).2.2

namespace IsNondegenerateQuadraticFamily

variable {ι : Type*} {Q : ι → QuadraticForm ℝ V}

/-- **Williamson's classification, elliptic–hyperbolic case.** If the span of a nondegenerate
family `Q` of quadratic forms contains a form `P` such that the square of its Hamiltonian
endomorphism has `dim V / 2` distinct nonzero real eigenvalues, then there are a Darboux basis and
a set `t` of planes whose elliptic–hyperbolic blocks, elliptic on the planes of `t` and hyperbolic
on the others, span the same space as `Q`. -/
theorem exists_isDarbouxBasis_span_eq_span_ellipticHyperbolic
    (h : ω.IsNondegenerateQuadraticFamily Q) {P : QuadraticForm ℝ V}
    (hP : P ∈ Submodule.span ℝ (Set.range Q)) {s : Finset ℝ} (hs : s.card * 2 = finrank ℝ V)
    (hs0 : (0 : ℝ) ∉ s) (hPs : ∀ μ ∈ s, (ω.hamiltonianEnd P ^ 2).HasEigenvalue μ) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (t : Finset (Fin n)), ω.IsDarbouxBasis b ∧
      Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (ellipticHyperbolic b t)) := by
  obtain ⟨n, b, t, c, hb, hc0, hμ, -, rfl⟩ :=
    ω.exists_isDarbouxBasis_eq_sum_smul_ellipticHyperbolic hs hs0 hPs
  refine ⟨n, b, t, hb, h.span_eq_of_span_le (hb.quadraticPoissonBracket_ellipticHyperbolic t)
    (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨i, rfl⟩
  -- `Q i` Poisson-commutes with the regular element `∑ₖ cₖ Bₖ`, so it is a combination of the
  -- `Bₖ`.
  refine hb.mem_span_ellipticHyperbolic_of_quadraticPoissonBracket_eq_zero t
    (fun k l hkl hkt hsq ↦ hkl (hμ ?_)) hc0
    (ω.quadraticPoissonBracket_eq_zero_of_mem_span h.quadraticPoissonBracket_eq_zero
      (Submodule.subset_span ⟨i, rfl⟩) hP)
  by_cases hk : k ∈ t
  · simp [hk, hkt.1 hk, hsq]
  · simp [hk, mt hkt.2 hk, hsq]

/-- **Nondegenerate families of elliptic–hyperbolic type.** The span of a nondegenerate family `Q`
of quadratic forms contains a form `P` such that the square of its Hamiltonian endomorphism has
`dim V / 2` distinct nonzero real eigenvalues exactly when it is the span of the
elliptic–hyperbolic blocks of some Darboux basis, for some set of elliptic planes. -/
theorem exists_mem_span_card_mul_two_eq_finrank_iff (h : ω.IsNondegenerateQuadraticFamily Q) :
    (∃ P ∈ Submodule.span ℝ (Set.range Q), ∃ s : Finset ℝ, s.card * 2 = finrank ℝ V ∧
        (0 : ℝ) ∉ s ∧ ∀ μ ∈ s, (ω.hamiltonianEnd P ^ 2).HasEigenvalue μ) ↔
      ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (t : Finset (Fin n)), ω.IsDarbouxBasis b ∧
        Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (ellipticHyperbolic b t)) := by
  refine ⟨fun ⟨P, hP, s, hs, hs0, hPs⟩ ↦
    h.exists_isDarbouxBasis_span_eq_span_ellipticHyperbolic hP hs hs0 hPs,
    fun ⟨n, b, t, hb, hspan⟩ ↦ ?_⟩
  -- The square of the Hamiltonian endomorphism of `∑ₖ (k + 1) Bₖ` is `∓(k + 1)²` on the `k`-th
  -- plane.
  let c : Fin n → ℝ := fun k ↦ k + 1
  let μ : Fin n → ℝ := fun k ↦ if k ∈ t then -c k ^ 2 else c k ^ 2
  have hc (k : Fin n) : 0 < c k := by positivity
  have hc2 : StrictMono fun k ↦ c k ^ 2 := fun k l hkl ↦ by
    dsimp only [c]; gcongr; exact_mod_cast hkl
  have hμ : Function.Injective μ := by
    intro k l hkl
    have hk := sq_pos_of_pos (hc k)
    have hl := sq_pos_of_pos (hc l)
    refine hc2.injective (?_ : c k ^ 2 = c l ^ 2)
    by_cases hkt : k ∈ t <;> by_cases hlt : l ∈ t <;>
      simp only [μ, hkt, hlt, ↓reduceIte] at hkl <;> linarith
  have hAA (k : Fin n) :
      ω.hamiltonianEnd (∑ k, c k • ellipticHyperbolic b t k)
        (ω.hamiltonianEnd (∑ k, c k • ellipticHyperbolic b t k) (b (k, 0))) = μ k • b (k, 0) := by
    rw [hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_fst]
    by_cases hk : k ∈ t
    · simp only [hk, ↓reduceIte, μ]
      rw [map_smul, hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_snd]
      simp [hk, smul_smul, sq]
    · simp only [hk, ↓reduceIte, μ]
      rw [map_smul, hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_fst]
      simp [hk, smul_smul, sq]
  refine ⟨∑ k, c k • ellipticHyperbolic b t k, ?_, Finset.univ.image μ, ?_, ?_, ?_⟩
  · rw [hspan]
    exact Submodule.sum_mem _ fun k _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · simp [Finset.card_image_of_injective _ hμ, finrank_eq_card_basis b]
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro k hk
    by_cases hkt : k ∈ t <;> simp only [μ, hkt, ↓reduceIte] at hk <;>
      nlinarith [sq_pos_of_pos (hc k)]
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index]
    rintro _ k rfl
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := b (k, 0))
      ⟨Module.End.mem_eigenspace_iff.2 ?_, b.ne_zero _⟩
    rw [sq, mul_apply_eq_comp, hAA]

end IsNondegenerateQuadraticFamily

end TauCeti.SymplecticForm
