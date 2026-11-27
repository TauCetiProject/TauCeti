/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Mixed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Semisimple
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Splitting
import TauCeti.LinearAlgebra.SesquilinearForm.AdjointPair

/-!
# Regular elements of nondegenerate families and Williamson's classification

Let `(V, ω)` be a finite-dimensional real symplectic vector space and `Q` a nondegenerate family of
quadratic forms on it (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily`): the Hamiltonian
endomorphisms `A_{Q i}` generate a Cartan subalgebra `𝔥` of `sp(V, ω)`. This file shows that the
span of `Q` contains a **regular element**: a form `P` such that `A_P²` has distinct nonzero real
eigenvalues `μ ∈ s`, `A_P` has distinct eigenvalues `a + b i`, `a, b > 0`, in a set `t`, and
`2 |s| + 4 |t| = dim V`
(`IsNondegenerateQuadraticFamily.exists_mem_span_card_mul_two_add_card_mul_four_eq_finrank`).
Equivalently, all `2n` complex eigenvalues of `A_P` are distinct. With the classification of
families admitting such an element
(`IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_williamsonBlocks_of_mem_span`),
this gives **Williamson's classification** of the Cartan subalgebras of `sp(V, ω)`: every
nondegenerate family spans the same space as the elliptic, hyperbolic and focus-focus Williamson
blocks of some Darboux basis
(`IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_williamsonBlocks`).

The proof is by induction on the dimension, entirely over `ℝ`.

* **Splitting.** If a symplectic subspace `L ≠ 0, V` is preserved by the family, the restrictions
  of the family to `L` and `L^ω` are nondegenerate, so they have regular elements `P₁` and `P₂` by
  induction. The form equal to `P₁` on `L` and to `c P₂` on `L^ω` lies in the span of the family,
  and it is regular for every `c > 0` outside a finite set, which keeps the eigenvalues of the two
  summands apart.
* **The irreducible case.** Otherwise every `ω`-self-adjoint endomorphism `E` commuting with the
  family has a symplectic generalized kernel preserved by the family, so it is injective or
  nilpotent. Since the family spans its own centralizer in `sp(V, ω)`, whose elements are
  semisimple, a nilpotent such `E` is zero: `A E` would be a nilpotent element of `𝔥` for an
  injective `A ∈ 𝔥`. So these `E` form a commutative algebra in which every nonzero element is
  invertible, and each is a real scalar or `a + b J` for a complex structure `J`, unique up to
  sign. If all are real scalars, then `𝔥 = ℝ A` with `A² = μ ≠ 0`, and the plane spanned by `v`
  and `A v` is symplectic and preserved by the family whenever `ω (A v) v ≠ 0`; so `V` is a plane.
  Otherwise some `A₀ ∈ 𝔥` has `A₀² = (a + b J)²` with `a, b > 0`, the kernels of `A₀ ∓ (a + b J)`
  are complementary isotropic subspaces, and vectors `v`, `u` in them with `ω v u ≠ 0` give a
  symplectic subspace spanned by `v, J v, u, J u` preserved by `𝔥 = span (A₀, J A₀)`; so `V` has
  dimension four and `A₀` is a regular focus-focus element.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
-/

public section

open Module Polynomial

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {ω : SymplecticForm V}
  {ι : Type*} {Q : ι → QuadraticForm ℝ V}

namespace IsNondegenerateQuadraticFamily

/-! ### Skew-adjoint and self-adjoint endomorphisms commuting with the family -/

variable (ω Q) in
/-- `X` lies in `sp(V, ω)` and commutes with the Hamiltonian endomorphisms of the family. For a
nondegenerate family these are the Hamiltonian endomorphisms of the forms in its span. -/
private def IsSkewCentral (X : Module.End ℝ V) : Prop :=
  X ∈ skewAdjointLieSubalgebra ω.toBilinForm ∧ ∀ i, Commute X (ω.hamiltonianEnd (Q i))

variable (ω Q) in
/-- `E` is `ω`-self-adjoint and commutes with the Hamiltonian endomorphisms of the family. -/
private def IsSymmCentral (E : Module.End ℝ V) : Prop :=
  LinearMap.IsAdjointPair ω.toBilinForm ω.toBilinForm E E ∧ ∀ i, Commute E (ω.hamiltonianEnd (Q i))

private theorem isSkewCentral_hamiltonianEnd (h : ω.IsNondegenerateQuadraticFamily Q)
    {R : QuadraticForm ℝ V} (hR : R ∈ Submodule.span ℝ (Set.range Q)) :
    IsSkewCentral ω Q (ω.hamiltonianEnd R) :=
  ⟨ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra R, fun i ↦ ω.quadraticPoissonBracket_eq_zero_iff.1
    (ω.quadraticPoissonBracket_eq_zero_of_mem_span h.quadraticPoissonBracket_eq_zero hR
      (Submodule.subset_span ⟨i, rfl⟩))⟩

private theorem IsSkewCentral.commute (h : ω.IsNondegenerateQuadraticFamily Q)
    {X Y : Module.End ℝ V} (hX : IsSkewCentral ω Q X) (hY : IsSkewCentral ω Q Y) :
    Commute X Y := by
  obtain ⟨R, hR, rfl⟩ := h.exists_mem_span_hamiltonianEnd_eq hX.1 hX.2
  obtain ⟨R', hR', rfl⟩ := h.exists_mem_span_hamiltonianEnd_eq hY.1 hY.2
  exact ω.quadraticPoissonBracket_eq_zero_iff.1
    (ω.quadraticPoissonBracket_eq_zero_of_mem_span h.quadraticPoissonBracket_eq_zero hR hR')

private theorem IsSkewCentral.isSemisimple (h : ω.IsNondegenerateQuadraticFamily Q)
    {X : Module.End ℝ V} (hX : IsSkewCentral ω Q X) : X.IsSemisimple := by
  obtain ⟨R, hR, rfl⟩ := h.exists_mem_span_hamiltonianEnd_eq hX.1 hX.2
  exact h.isSemisimple_hamiltonianEnd hR

private theorem IsSymmCentral.commute (h : ω.IsNondegenerateQuadraticFamily Q)
    {E X : Module.End ℝ V} (hE : IsSymmCentral ω Q E) (hX : IsSkewCentral ω Q X) :
    Commute E X := by
  obtain ⟨R, hR, rfl⟩ := h.exists_mem_span_hamiltonianEnd_eq hX.1 hX.2
  exact ω.commute_hamiltonianEnd_of_mem_span hE.2 hR

private theorem IsSkewCentral.mul_isSymmCentral (h : ω.IsNondegenerateQuadraticFamily Q)
    {X E : Module.End ℝ V} (hX : IsSkewCentral ω Q X) (hE : IsSymmCentral ω Q E) :
    IsSkewCentral ω Q (X * E) := by
  have hc (v : V) : X (E v) = E (X v) := LinearMap.congr_fun (hE.commute h hX).symm.eq v
  have hX' := (LinearMap.mem_skewAdjointSubmodule _).1 hX.1
  refine ⟨(LinearMap.mem_skewAdjointSubmodule _).2 fun x y ↦ ?_, fun i ↦ (hX.2 i).mul_left (hE.2 i)⟩
  simp only [mul_apply_eq_comp, Pi.neg_apply]
  rw [hX', hE.1, Pi.neg_apply, map_neg, map_neg, hc]
  simp

private theorem IsSkewCentral.mul (h : ω.IsNondegenerateQuadraticFamily Q)
    {X Y : Module.End ℝ V} (hX : IsSkewCentral ω Q X) (hY : IsSkewCentral ω Q Y) :
    IsSymmCentral ω Q (X * Y) := by
  have hc (v : V) : X (Y v) = Y (X v) := LinearMap.congr_fun (hX.commute h hY).eq v
  have hX' := (LinearMap.mem_skewAdjointSubmodule _).1 hX.1
  have hY' := (LinearMap.mem_skewAdjointSubmodule _).1 hY.1
  refine ⟨fun x y ↦ ?_, fun i ↦ (hX.2 i).mul_left (hY.2 i)⟩
  simp only [mul_apply_eq_comp]
  rw [hX', Pi.neg_apply, map_neg, hY', Pi.neg_apply, map_neg, neg_neg, hc]

private theorem IsSkewCentral.add {X Y : Module.End ℝ V} (hX : IsSkewCentral ω Q X)
    (hY : IsSkewCentral ω Q Y) : IsSkewCentral ω Q (X + Y) :=
  ⟨add_mem hX.1 hY.1, fun i ↦ (hX.2 i).add_left (hY.2 i)⟩

private theorem IsSymmCentral.add {E E' : Module.End ℝ V} (hE : IsSymmCentral ω Q E)
    (hE' : IsSymmCentral ω Q E') : IsSymmCentral ω Q (E + E') :=
  ⟨by simpa using hE.1.add hE'.1, fun i ↦ (hE.2 i).add_left (hE'.2 i)⟩

private theorem IsSymmCentral.smul {E : Module.End ℝ V} (hE : IsSymmCentral ω Q E) (c : ℝ) :
    IsSymmCentral ω Q (c • E) :=
  ⟨by simpa using hE.1.smul c, fun i ↦ (hE.2 i).smul_left c⟩

private theorem isSymmCentral_algebraMap (c : ℝ) :
    IsSymmCentral ω Q (algebraMap ℝ (Module.End ℝ V) c) :=
  ⟨fun x y ↦ by simp, fun _ ↦ Algebra.commute_algebraMap_left c _⟩

private theorem IsSymmCentral.sub {E E' : Module.End ℝ V} (hE : IsSymmCentral ω Q E)
    (hE' : IsSymmCentral ω Q E') : IsSymmCentral ω Q (E - E') := by
  simpa [sub_eq_add_neg] using hE.add (hE'.smul (-1))

private theorem IsSymmCentral.mul_of_commute {E E' : Module.End ℝ V} (hE : IsSymmCentral ω Q E)
    (hE' : IsSymmCentral ω Q E') (hc : Commute E E') : IsSymmCentral ω Q (E * E') := by
  refine ⟨fun x y ↦ ?_, fun i ↦ (hE.2 i).mul_left (hE'.2 i)⟩
  simp only [mul_apply_eq_comp]
  rw [hE.1, hE'.1]
  exact congrArg _ (LinearMap.congr_fun hc.eq y).symm

private theorem IsSymmCentral.aeval {E : Module.End ℝ V} (hE : IsSymmCentral ω Q E) (p : ℝ[X]) :
    IsSymmCentral ω Q (aeval E p) :=
  ⟨hE.1.aeval p, fun i ↦
    (Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton ℝ _)
      (hE.2 i).symm).symm⟩

/-! ### Irreducible families -/

variable (ω Q) in
/-- A family is **irreducible** when no symplectic subspace other than `0` and `V` is preserved
by all its Hamiltonian endomorphisms. -/
private def IsIrreducible : Prop :=
  ∀ L : Submodule ℝ V, ω.IsSymplectic L →
    (∀ i, L ∈ Module.End.invtSubmodule (ω.hamiltonianEnd (Q i))) → L = ⊥ ∨ L = ⊤

/-- For an irreducible family, an `ω`-self-adjoint endomorphism commuting with the family is
injective or nilpotent: its generalized kernel is a symplectic subspace preserved by the
family. -/
private theorem IsSymmCentral.injective_or_isNilpotent (hirr : IsIrreducible ω Q)
    {E : Module.End ℝ V} (hE : IsSymmCentral ω Q E) :
    Function.Injective E ∨ IsNilpotent E := by
  have hsymp : ω.IsSymplectic (E.maxGenEigenspace 0) :=
    isSymplectic_iff_nondegenerate_restrict.2 <|
      LinearMap.IsAdjointPair.nondegenerate_domRestrict₁₂_maxGenEigenspace ω.nondegenerate hE.1 0
  rcases hirr _ hsymp fun i ↦ (Module.End.mem_invtSubmodule _).2
    (Module.End.mapsTo_maxGenEigenspace_of_comm (hE.2 i) 0) with h0 | htop
  · refine Or.inl (LinearMap.ker_eq_bot.1 (eq_bot_iff.2 fun v hv ↦ ?_))
    rw [← h0]
    exact Module.End.eigenspace_le_maxGenEigenspace (by simpa using hv)
  · refine Or.inr ⟨E.maxGenEigenspaceIndex 0, LinearMap.ker_eq_top.1 ?_⟩
    rw [← htop, Module.End.maxGenEigenspace_eq]
    simp

/-- For an irreducible nondegenerate family, every nonzero element of `sp(V, ω)` commuting with
the family is injective. -/
private theorem IsSkewCentral.eq_zero_or_injective (h : ω.IsNondegenerateQuadraticFamily Q)
    (hirr : IsIrreducible ω Q) {X : Module.End ℝ V} (hX : IsSkewCentral ω Q X) :
    X = 0 ∨ Function.Injective X := by
  rcases (hX.mul h hX).injective_or_isNilpotent hirr with hinj | ⟨n, hn⟩
  · exact Or.inr (Function.Injective.of_comp (f := X) hinj)
  · refine Or.inl (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨2 * n, ?_⟩
      (hX.isSemisimple h))
    rw [pow_mul, sq, hn]

/-- For an irreducible nondegenerate family with an injective element `A`, every self-adjoint
endomorphism commuting with the family is zero or injective. -/
private theorem IsSymmCentral.eq_zero_or_injective (h : ω.IsNondegenerateQuadraticFamily Q)
    (hirr : IsIrreducible ω Q) {A : Module.End ℝ V} (hA : IsSkewCentral ω Q A)
    (hAi : Function.Injective A) {E : Module.End ℝ V} (hE : IsSymmCentral ω Q E) :
    E = 0 ∨ Function.Injective E := by
  rcases hE.injective_or_isNilpotent hirr with hinj | hnil
  · exact Or.inr hinj
  -- `A E` is semisimple and nilpotent, hence zero.
  have hAE := hA.mul_isSymmCentral h hE
  have h0 : A * E = 0 := Module.End.eq_zero_of_isNilpotent_isSemisimple
    ((hE.commute h hA).symm.isNilpotent_mul_left hnil) (hAE.isSemisimple h)
  refine Or.inl (LinearMap.ext fun x ↦ hAi ?_)
  simpa using LinearMap.congr_fun h0 x

/-- Self-adjoint endomorphisms commuting with an irreducible nondegenerate family with an
injective element commute with each other. -/
private theorem IsSymmCentral.commute_of_injective (h : ω.IsNondegenerateQuadraticFamily Q)
    {A : Module.End ℝ V} (hA : IsSkewCentral ω Q A) (hAi : Function.Injective A)
    {E E' : Module.End ℝ V} (hE : IsSymmCentral ω Q E) (hE' : IsSymmCentral ω Q E') :
    Commute E E' := by
  have hc := (hA.mul_isSymmCentral h hE).commute h (hA.mul_isSymmCentral h hE')
  have hAE := hE.commute h hA
  have hAE' := hE'.commute h hA
  refine LinearMap.ext fun x ↦ hAi (hAi ?_)
  have := LinearMap.congr_fun hc.eq x
  simp only [mul_apply_eq_comp] at this ⊢
  have h₁ (y : V) : E (A y) = A (E y) := LinearMap.congr_fun hAE.eq y
  have h₂ (y : V) : E' (A y) = A (E' y) := LinearMap.congr_fun hAE'.eq y
  rwa [h₁, h₂] at this

/-- A polynomial identity behind the complex structure attached to a nonreal root `z` of a real
polynomial: `((X - re z) / im z)² + 1 = (X² - 2 re z X + |z|²) / (im z)²`. -/
private theorem sq_add_one_eq_C_mul_quadratic {z : ℂ} (hz : z.im ≠ 0) :
    (C z.im⁻¹ * (X - C z.re)) * (C z.im⁻¹ * (X - C z.re)) + 1 =
      C (z.im⁻¹ ^ 2) * (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)) := by
  have hb : C z.im⁻¹ * C z.im = (1 : ℝ[X]) := by rw [← C_mul, inv_mul_cancel₀ hz, C_1]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [map_add, map_mul, map_pow, C_ofNat]
  linear_combination (-(1 + C z.im⁻¹ * C z.im)) * hb

/-- **Self-adjoint endomorphisms commuting with an irreducible family are complex scalars.** For an
irreducible nondegenerate family with an injective element, a self-adjoint endomorphism commuting
with the family is a real scalar, or it is `a + b J` for a self-adjoint `J` commuting with the
family with `J² = -1`: every polynomial in it is zero or injective, so its minimal polynomial has a
single real root or a single pair of conjugate complex roots. -/
private theorem IsSymmCentral.eq_algebraMap_or_exists (h : ω.IsNondegenerateQuadraticFamily Q)
    (hirr : IsIrreducible ω Q) {A : Module.End ℝ V} (hA : IsSkewCentral ω Q A)
    (hAi : Function.Injective A) [Nontrivial V] {E : Module.End ℝ V} (hE : IsSymmCentral ω Q E) :
    (∃ c : ℝ, E = algebraMap ℝ _ c) ∨ ∃ J : Module.End ℝ V, IsSymmCentral ω Q J ∧ J * J = -1 ∧
      ∃ a b : ℝ, E = algebraMap ℝ _ a + b • J := by
  have hint : IsIntegral ℝ E := Algebra.IsIntegral.isIntegral E
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ (minpoly ℝ E) (minpoly.degree_pos hint).ne'
  by_cases him : z.im = 0
  · -- A real root `z` of the minimal polynomial is an eigenvalue, and `E - z` is not injective.
    refine Or.inl ⟨z.re, ?_⟩
    have hroot : (minpoly ℝ E).IsRoot z.re := by
      have hz' : (algebraMap ℝ ℂ z.re) = z := Complex.ext (by simp) (by simp [him])
      rw [← hz', aeval_algebraMap_apply_eq_algebraMap_eval] at hz
      simpa using hz
    obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_of_isRoot hroot).exists_hasEigenvector
    rcases (hE.sub (isSymmCentral_algebraMap z.re)).eq_zero_or_injective h hirr hA hAi with
      h0 | hinj
    · exact sub_eq_zero.1 h0
    · exact absurd (hinj (by simpa [sub_eq_zero] using hv.apply_eq_smul)) hv.2
  · -- The real quadratic `q` with roots `z` and its conjugate divides the minimal polynomial,
    -- and `q(E) = 0`.
    obtain ⟨r, hr⟩ := Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero _ hz him
    set q : ℝ[X] := X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)
    have hq0 : Polynomial.aeval E q = 0 := by
      rcases (hE.aeval q).eq_zero_or_injective h hirr hA hAi with h0 | hinj
      · exact h0
      exfalso
      have hr0 : Polynomial.aeval E r = 0 := LinearMap.ext fun x ↦ hinj <| by
        have := LinearMap.congr_fun (minpoly.aeval ℝ E) x
        rw [hr, map_mul] at this
        simpa using this
      have hrne : r ≠ 0 := by
        rintro rfl
        exact minpoly.ne_zero hint (by simpa using hr)
      have hdvd : q * r ∣ 1 * r := by simpa [← hr] using minpoly.dvd ℝ E hr0
      have hq : IsUnit q := isUnit_of_dvd_one ((mul_dvd_mul_iff_right hrne).1 hdvd)
      have hdeg : q.natDegree = 2 := by
        simp only [q]
        compute_degree!
      rw [natDegree_eq_zero_of_isUnit hq] at hdeg
      exact absurd hdeg (by norm_num)
    refine Or.inr ⟨Polynomial.aeval E (C z.im⁻¹ * (X - C z.re)), hE.aeval _, ?_, z.re, z.im, ?_⟩
    · have := congrArg (Polynomial.aeval E) (sq_add_one_eq_C_mul_quadratic him)
      rw [map_add, map_one, map_mul (Polynomial.aeval E) (C (z.im⁻¹ ^ 2)), hq0, mul_zero,
        map_mul (Polynomial.aeval E) (C z.im⁻¹ * (X - C z.re))] at this
      exact eq_neg_of_add_eq_zero_left this
    · have hX : (X : ℝ[X]) = C z.re + z.im • (C z.im⁻¹ * (X - C z.re)) := by
        rw [smul_eq_C_mul, ← mul_assoc, ← C_mul, mul_inv_cancel₀ him, C_1, one_mul]
        ring
      have := congrArg (Polynomial.aeval E) hX
      rwa [aeval_X, map_add, map_smul, aeval_C] at this

/-- Two complex structures `J`, `J'` commuting with an irreducible nondegenerate family with an
injective element agree up to sign: `(J J' - 1)(J J' + 1) = J² J'² - 1 = 0`. -/
private theorem eq_or_eq_neg_of_mul_self_eq_neg_one (h : ω.IsNondegenerateQuadraticFamily Q)
    (hirr : IsIrreducible ω Q) {A : Module.End ℝ V} (hA : IsSkewCentral ω Q A)
    (hAi : Function.Injective A) {J J' : Module.End ℝ V} (hJ : IsSymmCentral ω Q J)
    (hJ' : IsSymmCentral ω Q J') (hJJ : J * J = -1) (hJJ' : J' * J' = -1) : J' = J ∨ J' = -J := by
  have hc := hJ.commute_of_injective h hA hAi hJ'
  have hK := hJ.mul_of_commute hJ' hc
  have hprod : (J * J' - 1) * (J * J' + 1) = 0 := by
    have : J * J' * (J * J') = 1 := by
      rw [mul_assoc, ← mul_assoc J' J, ← hc.eq, mul_assoc, ← mul_assoc, hJJ, hJJ']
      simp
    rw [sub_mul, mul_add, mul_add, this]
    simp only [mul_one, one_mul]
    abel
  have hJJ'' (c : Module.End ℝ V) (hc' : J * J' = c) : J' = -(J * c) := by
    rw [← hc', ← mul_assoc, hJJ]
    simp
  rcases (hK.sub (isSymmCentral_algebraMap 1)).eq_zero_or_injective h hirr hA hAi with h0 | hinj
  · refine Or.inr ?_
    rw [hJJ'' 1 (by simpa [sub_eq_zero] using h0), mul_one]
  · refine Or.inl ?_
    have h1 : J * J' + 1 = 0 := LinearMap.ext fun x ↦ hinj <| by
      simpa [Algebra.algebraMap_eq_smul_one] using LinearMap.congr_fun hprod x
    rw [hJJ'' (-1) (eq_neg_of_add_eq_zero_left h1)]
    simp

/-! ### The irreducible case -/

omit [FiniteDimensional ℝ V] in
private theorem hasEigenvalue_sq_of_apply {A : Module.End ℝ V} {v : V} (hv : v ≠ 0) {μ : ℝ}
    (h : A (A v) = μ • v) : (A ^ 2).HasEigenvalue μ :=
  Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (by rwa [sq]), hv⟩

/-- The spectral condition on the Hamiltonian endomorphism `A = A_P` of a regular element `P` used
by `IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_williamsonBlocks_of_mem_span`:
`A²` has distinct nonzero real eigenvalues `μ ∈ s`, `A` has distinct eigenvalues `z ∈ t` in the open
first quadrant, and `2 |s| + 4 |t| = dim V`. -/
private def HasRegularSpectrum (A : Module.End ℝ V) : Prop :=
  ∃ (s : Finset ℝ) (t : Finset ℂ), s.card * 2 + t.card * 4 = finrank ℝ V ∧ (0 : ℝ) ∉ s ∧
    (∀ μ ∈ s, (A ^ 2).HasEigenvalue μ) ∧ (∀ z ∈ t, 0 < z.re ∧ 0 < z.im) ∧
    ∀ z ∈ t, ∃ v w : V, v ≠ 0 ∧ A v = z.re • v - z.im • w ∧ A w = z.im • v + z.re • w

omit [FiniteDimensional ℝ V] in
/-- Let `A₀ ∈ sp(V, ω)` commute with a self-adjoint `K` with `K² = -1`. The vectors on which `A₀`
acts as `a + b K`, for `(a, b) ≠ 0`, pair to zero under `ω`. -/
private theorem apply_eq_zero_of_apply_eq_smul_add_smul {A₀ K : Module.End ℝ V}
    (hA₀ : A₀ ∈ skewAdjointLieSubalgebra ω.toBilinForm)
    (hK : LinearMap.IsAdjointPair ω.toBilinForm ω.toBilinForm K K) (hKK : ∀ v, K (K v) = -v)
    (hKA : ∀ v, A₀ (K v) = K (A₀ v)) {a b : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0) {v v' : V}
    (hv : A₀ v = a • v + b • K v) (hv' : A₀ v' = a • v' + b • K v') : ω v v' = 0 := by
  have hA₀' := (LinearMap.mem_skewAdjointSubmodule _).1 hA₀
  -- For `w` with `A₀ w = a w + b K w`, `ω (A₀ v) w = -ω v (A₀ w)` reads
  -- `a ω(v, w) + b ω(v, K w) = 0`.
  have key (w : V) (hw : A₀ w = a • w + b • K w) : a * ω v w + b * ω v (K w) = 0 := by
    have h1 : ω (A₀ v) w = -ω v (A₀ w) := by simpa using hA₀' v w
    have h2 : ω (K v) w = ω v (K w) := hK v w
    rw [hv, hw] at h1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      h2] at h1
    linarith
  have e₁ := key v' hv'
  have e₂ := key (K v') (by rw [hKA, hv', map_add, map_smul, map_smul])
  simp only [hKK, map_neg] at e₂
  beta_reduce at e₁ e₂ ⊢
  have : (a ^ 2 + b ^ 2) * ω.toBilinForm v v' = 0 := by linear_combination a * e₁ - b * e₂
  exact (mul_eq_zero.1 this).resolve_left hab

omit [FiniteDimensional ℝ V] in
/-- In the plane-pair configuration of the focus-focus case, a combination of `v, K v, u, K u`
pairing to zero with all four vectors is trivial. -/
private theorem eq_zero_of_apply_four {K : Module.End ℝ V} {v u : V}
    (hK : LinearMap.IsAdjointPair ω.toBilinForm ω.toBilinForm K K) (hKK : ∀ v, K (K v) = -v)
    (hv : ω v (K v) = 0) (hu : ω u (K u) = 0) (hvu : ω v u ≠ 0) {α β γ δ : ℝ}
    (h₁ : ω (α • v + β • K v + γ • u + δ • K u) u = 0)
    (h₂ : ω (α • v + β • K v + γ • u + δ • K u) (K u) = 0)
    (h₃ : ω v (α • v + β • K v + γ • u + δ • K u) = 0)
    (h₄ : ω (K v) (α • v + β • K v + γ • u + δ • K u) = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 ∧ δ = 0 := by
  have hKuu : ω (K u) u = 0 := by rw [← ω.neg_eq, hu, neg_zero]
  have hKvv : ω (K v) v = 0 := by rw [← ω.neg_eq, hv, neg_zero]
  have hself (x : V) : ω.toBilinForm x x = 0 := ω.self_eq_zero x
  beta_reduce at hv hu hvu hKuu hKvv h₁ h₂ h₃ h₄
  have hKvu : ω.toBilinForm (K v) u = ω.toBilinForm v (K u) := hK v u
  have hKvKu : ω.toBilinForm (K v) (K u) = -ω.toBilinForm v u := by
    rw [hK v (K u), hKK, map_neg]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hself, hKvu, hKvKu, hKuu, hKvv, hv, hu, mul_zero, add_zero, zero_add] at h₁ h₂ h₃ h₄
  set p := ω.toBilinForm v u
  set q := ω.toBilinForm v (K u)
  have hp : p ^ 2 + q ^ 2 ≠ 0 := by positivity
  have hα : (p ^ 2 + q ^ 2) * α = 0 := by linear_combination p * h₁ + q * h₂
  have hβ : (p ^ 2 + q ^ 2) * β = 0 := by linear_combination q * h₁ - p * h₂
  have hγ : (p ^ 2 + q ^ 2) * γ = 0 := by linear_combination p * h₃ + q * h₄
  have hδ : (p ^ 2 + q ^ 2) * δ = 0 := by linear_combination q * h₃ - p * h₄
  exact ⟨(mul_eq_zero.1 hα).resolve_left hp, (mul_eq_zero.1 hβ).resolve_left hp,
    (mul_eq_zero.1 hγ).resolve_left hp, (mul_eq_zero.1 hδ).resolve_left hp⟩

omit [FiniteDimensional ℝ V] in
/-- In the plane-pair configuration of the focus-focus case, `v, K v, u, K u` are linearly
independent and span a symplectic subspace. -/
private theorem linearIndependent_and_isSymplectic_span_range_four {K : Module.End ℝ V} {v u : V}
    (hK : LinearMap.IsAdjointPair ω.toBilinForm ω.toBilinForm K K) (hKK : ∀ v, K (K v) = -v)
    (hv : ω v (K v) = 0) (hu : ω u (K u) = 0) (hvu : ω v u ≠ 0) :
    LinearIndependent ℝ ![v, K v, u, K u] ∧
      ω.IsSymplectic (Submodule.span ℝ (Set.range ![v, K v, u, K u])) := by
  set f : Fin 4 → V := ![v, K v, u, K u]
  have hcoef (c : Fin 4 → ℝ) (h₁ : ω (∑ i, c i • f i) u = 0) (h₂ : ω (∑ i, c i • f i) (K u) = 0)
      (h₃ : ω v (∑ i, c i • f i) = 0) (h₄ : ω (K v) (∑ i, c i • f i) = 0) : c = 0 := by
    simp only [Fin.sum_univ_four, f, Matrix.cons_val] at h₁ h₂ h₃ h₄
    obtain ⟨h0, h1, h2, h3⟩ := eq_zero_of_apply_four hK hKK hv hu hvu h₁ h₂ h₃ h₄
    ext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  refine ⟨Fintype.linearIndependent_iff.2 fun c hc ↦
    congrFun (hcoef c (by simp [hc]) (by simp [hc]) (by simp [hc]) (by simp [hc])), ?_⟩
  rw [isSymplectic_iff_disjoint, Submodule.disjoint_def]
  intro x hx hxo
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
  have ho (k : Fin 4) := mem_orthogonal_iff.1 hxo (f k) (Submodule.subset_span ⟨k, rfl⟩)
  have h₂ : f 2 = u := rfl
  have h₃ : f 3 = K u := rfl
  rw [hcoef c (by rw [← ω.neg_eq, ← h₂, ho 2, neg_zero])
    (by rw [← ω.neg_eq, ← h₃, ho 3, neg_zero]) (ho 0) (ho 1)]
  simp

/-- **The irreducible case with real scalars.** If every self-adjoint endomorphism commuting with
an irreducible nondegenerate family is a real scalar, then `V` is a symplectic plane and every
form `P` of the span with injective `A_P` is regular, with `A_P² = μ ≠ 0`: for `v` with
`ω (A_P v) v ≠ 0`, the plane spanned by `v` and `A_P v` is symplectic and preserved by the family,
whose Hamiltonian endomorphisms are multiples of `A_P`. -/
private theorem hasRegularSpectrum_of_forall_eq_algebraMap (h : ω.IsNondegenerateQuadraticFamily Q)
    (hirr : IsIrreducible ω Q) [Nontrivial V] {P : QuadraticForm ℝ V}
    (hP : P ∈ Submodule.span ℝ (Set.range Q)) (hAi : Function.Injective (ω.hamiltonianEnd P))
    (hscalar : ∀ E, IsSymmCentral ω Q E → ∃ c : ℝ, E = algebraMap ℝ _ c) :
    HasRegularSpectrum (ω.hamiltonianEnd P) := by
  set A := ω.hamiltonianEnd P
  have hA := isSkewCentral_hamiltonianEnd h hP
  obtain ⟨μ, hμ⟩ := hscalar _ (hA.mul h hA)
  have hAA (x : V) : A (A x) = μ • x := by simpa using LinearMap.congr_fun hμ x
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hv₀ (hAi (hAi (by simpa using hAA v₀)))
  -- Each `A_{Q i}` is a multiple of `A`, since `A A_{Q i}` is a real scalar.
  have hmul (i : ι) : ∃ c : ℝ, ∀ x, ω.hamiltonianEnd (Q i) x = c • A x := by
    obtain ⟨c, hc⟩ := hscalar _ (hA.mul h (isSkewCentral_hamiltonianEnd h
      (Submodule.subset_span ⟨i, rfl⟩)))
    refine ⟨μ⁻¹ * c, fun x ↦ ?_⟩
    have e₁ := hAA (ω.hamiltonianEnd (Q i) x)
    rw [show A (ω.hamiltonianEnd (Q i) x) = c • x by simpa using LinearMap.congr_fun hc x,
      map_smul] at e₁
    rw [mul_smul, e₁, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  -- A vector `v` with `ω (A v) v = 2 P v ≠ 0`.
  obtain ⟨v, hv⟩ : ∃ v, P v ≠ 0 := by
    by_contra! H
    have hP0 : P = 0 := QuadraticMap.ext H
    exact hv₀ (hAi (by simp [A, hP0]))
  have hd : ω (A v) v ≠ 0 := by
    rw [apply_hamiltonianEnd, QuadraticMap.polar_self]
    simpa using hv
  set U := Submodule.span ℝ ({A v, v} : Set V)
  have hUinv (i : ι) : U ∈ Module.End.invtSubmodule (ω.hamiltonianEnd (Q i)) := by
    obtain ⟨c, hc⟩ := hmul i
    refine (Module.End.mem_invtSubmodule _).2 (Submodule.span_le.2 (Set.insert_subset_iff.2
      ⟨?_, Set.singleton_subset_iff.2 ?_⟩))
    · simpa [hc, hAA, smul_smul] using Submodule.smul_mem U (c * μ)
        (Submodule.subset_span (by simp))
    · simpa [hc] using Submodule.smul_mem U c (Submodule.subset_span (by simp))
  have hfin : finrank ℝ V = 2 := by
    rcases hirr U (isSymplectic_iff_disjoint.2 (ω.disjoint_span_pair_orthogonal hd)) hUinv with
      hU | hU
    · have hvU : v ∈ U := Submodule.subset_span (by simp)
      rw [hU, Submodule.mem_bot] at hvU
      simp [hvU] at hv
    · have h₁ : finrank ℝ U ≤ 2 := by
        classical
        exact (finrank_span_le_card ({A v, v} : Set V)).trans (by
          simpa using Finset.card_insert_le (A v) {v})
      rw [hU, finrank_top] at h₁
      have h₂ := Module.finrank_pos (R := ℝ) (M := V)
      obtain ⟨k, hk⟩ := ω.even_finrank
      omega
  refine ⟨{μ}, ∅, by simp [hfin], by simpa using hμ0.symm, fun μ' hμ' ↦ ?_, by simp, by simp⟩
  rw [Finset.mem_singleton.1 hμ']
  exact hasEigenvalue_sq_of_apply hv₀ (hAA v₀)

omit [FiniteDimensional ℝ V] in
/-- Let `A₀ ∈ sp(V, ω)` commute with a self-adjoint `K`, `K² = -1`, with
`A₀² = (a + b K)² = a² - b² + 2 a b K` for `a, b > 0`. The vectors with `A₀ v = (a + b K) v`
and those with `A₀ u = -(a + b K) u` meet only in `0`. -/
private theorem eq_zero_of_apply_eq_smul_add_smul_of_apply_eq_neg {K : Module.End ℝ V}
    {A₀ : Module.End ℝ V} (hKK : ∀ v, K (K v) = -v) {a b : ℝ} (ha : 0 < a) {x : V}
    (h₁ : A₀ x = a • x + b • K x) (h₂ : A₀ x = (-a) • x + (-b) • K x) : x = 0 := by
  have e : a • x + b • K x = 0 := by
    have := h₁.symm.trans h₂
    rw [neg_smul, neg_smul, ← neg_add, eq_neg_iff_add_eq_zero, ← two_smul ℝ] at this
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  have eK : a • K x - b • x = 0 := by
    have := congrArg K e
    rwa [map_add, map_smul, map_smul, hKK, smul_neg, ← sub_eq_add_neg, map_zero] at this
  have : (a ^ 2 + b ^ 2) • x = 0 := by
    rw [show (a ^ 2 + b ^ 2) • x = a • (a • x + b • K x) - b • (a • K x - b • x) by module, e, eK]
    simp
  exact (smul_eq_zero.1 this).resolve_left (by positivity)

/-- **The Lagrangian pair of a focus-focus element.** With `A₀`, `K`, `a`, `b` as in
`eq_zero_of_apply_eq_smul_add_smul_of_apply_eq_neg`, the kernels of `A₀ - (a + b K)` and
`A₀ + (a + b K)` are isotropic and span `V`, since their product is `A₀² - (a + b K)² = 0`. Hence
there are `v ≠ 0` in the first and `u` in the second with `ω v u ≠ 0`. -/
private theorem exists_apply_eq_smul_add_smul_and_apply_eq_neg [Nontrivial V]
    {A₀ K : Module.End ℝ V} (hA₀ : A₀ ∈ skewAdjointLieSubalgebra ω.toBilinForm)
    (hK : LinearMap.IsAdjointPair ω.toBilinForm ω.toBilinForm K K) (hKK : ∀ v, K (K v) = -v)
    (hKA : ∀ v, A₀ (K v) = K (A₀ v)) {a b : ℝ} (ha : 0 < a)
    (hAA : ∀ v, A₀ (A₀ v) = (a ^ 2 - b ^ 2) • v + (2 * a * b) • K v) :
    ∃ v u : V, v ≠ 0 ∧ A₀ v = a • v + b • K v ∧ A₀ u = (-a) • u + (-b) • K u ∧ ω v u ≠ 0 := by
  set D : Module.End ℝ V := algebraMap ℝ _ a + b • K
  have hD (v : V) : D v = a • v + b • K v := by simp [D, Algebra.algebraMap_eq_smul_one]
  have hM (v : V) : v ∈ LinearMap.ker (A₀ - D) ↔ A₀ v = a • v + b • K v := by
    simp [sub_eq_zero, hD]
  have hN (v : V) : v ∈ LinearMap.ker (A₀ + D) ↔ A₀ v = (-a) • v + (-b) • K v := by
    rw [LinearMap.mem_ker, LinearMap.add_apply, hD, add_eq_zero_iff_eq_neg, neg_add, neg_smul,
      neg_smul]
  have hab : a ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hab' : (-a) ^ 2 + (-b) ^ 2 ≠ 0 := by simpa using hab
  -- `range (A₀ + D) ≤ ker (A₀ - D)`, and the two kernels meet only in `0`.
  have hrange : LinearMap.range (A₀ + D) ≤ LinearMap.ker (A₀ - D) := by
    rintro _ ⟨x, rfl⟩
    rw [hM]
    simp only [LinearMap.add_apply, hD, map_add, map_smul, hKA, hAA, hKK]
    module
  have hinf : LinearMap.ker (A₀ - D) ⊓ LinearMap.ker (A₀ + D) = ⊥ :=
    eq_bot_iff.2 fun x hx ↦ (Submodule.mem_bot ℝ).2 <|
      eq_zero_of_apply_eq_smul_add_smul_of_apply_eq_neg hKK ha ((hM x).1 hx.1) ((hN x).1 hx.2)
  have hsup : LinearMap.ker (A₀ - D) ⊔ LinearMap.ker (A₀ + D) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
    have h₁ := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (A₀ - D))
      (LinearMap.ker (A₀ + D))
    have h₂ := LinearMap.finrank_range_add_finrank_ker (A₀ + D)
    have h₃ := Submodule.finrank_mono hrange
    rw [hinf, finrank_bot] at h₁
    omega
  have hisoM {x y : V} (hx : x ∈ LinearMap.ker (A₀ - D)) (hy : y ∈ LinearMap.ker (A₀ - D)) :
      ω x y = 0 :=
    apply_eq_zero_of_apply_eq_smul_add_smul hA₀ hK hKK hKA hab ((hM x).1 hx) ((hM y).1 hy)
  have hisoN {x y : V} (hx : x ∈ LinearMap.ker (A₀ + D)) (hy : y ∈ LinearMap.ker (A₀ + D)) :
      ω x y = 0 :=
    apply_eq_zero_of_apply_eq_smul_add_smul hA₀ hK hKK hKA hab' ((hN x).1 hx) ((hN y).1 hy)
  -- A vector `x` pairing nontrivially with `v` splits along the two kernels.
  have hpair (v : V) (hv : v ≠ 0) : ∃ x, ω v x ≠ 0 := by
    by_contra! H
    exact hv (ω.nondegenerate.1 v H)
  obtain ⟨v, hvM, hv⟩ : ∃ v ∈ LinearMap.ker (A₀ - D), v ≠ 0 := by
    by_contra! H
    have hN : LinearMap.ker (A₀ + D) = ⊤ := by
      rwa [(Submodule.eq_bot_iff _).2 H, bot_sup_eq] at hsup
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨y, hy⟩ := hpair x hx
    exact hy (hisoN (hN ▸ Submodule.mem_top) (hN ▸ Submodule.mem_top))
  obtain ⟨x, hx⟩ := hpair v hv
  obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : x ∈ _)
  refine ⟨v, u, hv, (hM v).1 hvM, (hN u).1 hu, fun hvu ↦ hx ?_⟩
  have hvy : ω v y = 0 := hisoM hvM hy
  beta_reduce at hvu hvy ⊢
  rw [map_add, hvy, hvu, add_zero]

/-- If every self-adjoint endomorphism commuting with the family lies in `ℝ + ℝ K`, `K² = -1`,
and `A₀² = x₀ + y₀ K` with `y₀ ≠ 0`, then every element `X` of `sp(V, ω)` commuting with the
family is a combination of `A₀` and `K A₀`: `A₀ X` is self-adjoint, hence `α + β K`, and `x₀ + y₀ K`
is invertible in `ℝ + ℝ K`. -/
private theorem IsSkewCentral.exists_apply_eq_smul_add_smul
    (h : ω.IsNondegenerateQuadraticFamily Q) {A₀ K X : Module.End ℝ V}
    (hA₀ : IsSkewCentral ω Q A₀) (hKK : ∀ v, K (K v) = -v)
    (hspanK : ∀ E, IsSymmCentral ω Q E → ∃ a b : ℝ, E = algebraMap ℝ _ a + b • K)
    {x₀ y₀ : ℝ} (hy₀ : y₀ ≠ 0) (hAA : ∀ v, A₀ (A₀ v) = x₀ • v + y₀ • K v)
    (hX : IsSkewCentral ω Q X) : ∃ p q : ℝ, ∀ w, X w = p • A₀ w + q • K (A₀ w) := by
  obtain ⟨α, β, hαβ⟩ := hspanK _ (hA₀.mul h hX)
  have hAX (v : V) : A₀ (X v) = α • v + β • K v := by
    simpa [Algebra.algebraMap_eq_smul_one] using LinearMap.congr_fun hαβ v
  have hXA (v : V) : X (A₀ v) = A₀ (X v) := LinearMap.congr_fun (hX.commute h hA₀).eq v
  have hc : x₀ ^ 2 + y₀ ^ 2 ≠ 0 := by positivity
  refine ⟨(x₀ ^ 2 + y₀ ^ 2)⁻¹ * (x₀ * α + y₀ * β), (x₀ ^ 2 + y₀ ^ 2)⁻¹ * (x₀ * β - y₀ * α),
    fun w ↦ ?_⟩
  -- `x₀ X w + y₀ K X w = A₀² X w = A₀ X (A₀ w) = α A₀ w + β K A₀ w`; apply `K` and solve.
  have e : x₀ • X w + y₀ • K (X w) = α • A₀ w + β • K (A₀ w) := by
    rw [← hAA, ← hXA, hAX]
  have eK := congrArg K e
  simp only [map_add, map_smul, hKK, smul_neg] at eK
  have key : (x₀ ^ 2 + y₀ ^ 2) • X w =
      (x₀ * α + y₀ * β) • A₀ w + (x₀ * β - y₀ * α) • K (A₀ w) := by
    linear_combination (norm := module) x₀ • e - y₀ • eK
  rw [mul_smul, mul_smul, ← smul_add, ← key, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **The irreducible case with a complex structure.** Let `A₀ = A_{P₀}` commute with a
self-adjoint `K`, `K² = -1`, such that every Hamiltonian endomorphism of the family is a combination
of `A₀` and `K A₀`. If `A₀ v = (a + b K) v` with `v ≠ 0` and `A₀ u = -(a + b K) u` with
`ω v u ≠ 0`, for `a, b > 0`, then `v, K v, u, K u` span a symplectic subspace preserved by the
family. For an irreducible family it is `V`, so `V` has dimension four and `P₀` is a regular
focus-focus element, with eigenvalue `a + b i`. -/
private theorem hasRegularSpectrum_of_apply_eq_smul_add_smul (hirr : IsIrreducible ω Q)
    {P₀ : QuadraticForm ℝ V} {K : Module.End ℝ V}
    (hK : LinearMap.IsAdjointPair ω.toBilinForm ω.toBilinForm K K) (hKK : ∀ v, K (K v) = -v)
    (hKA : ∀ v, ω.hamiltonianEnd P₀ (K v) = K (ω.hamiltonianEnd P₀ v))
    (hX : ∀ i, ∃ p q : ℝ, ∀ w, ω.hamiltonianEnd (Q i) w =
      p • ω.hamiltonianEnd P₀ w + q • K (ω.hamiltonianEnd P₀ w))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {v u : V} (hv0 : v ≠ 0)
    (hv : ω.hamiltonianEnd P₀ v = a • v + b • K v)
    (hu : ω.hamiltonianEnd P₀ u = (-a) • u + (-b) • K u) (hvu : ω v u ≠ 0) :
    HasRegularSpectrum (ω.hamiltonianEnd P₀) := by
  set A₀ := ω.hamiltonianEnd P₀
  have hA₀ := ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra P₀
  have hKv : A₀ (K v) = a • K v + b • K (K v) := by rw [hKA, hv, map_add, map_smul, map_smul]
  have hKu : A₀ (K u) = (-a) • K u + (-b) • K (K u) := by
    rw [hKA, hu, map_add, map_smul, map_smul]
  have hvKv : ω v (K v) = 0 :=
    apply_eq_zero_of_apply_eq_smul_add_smul hA₀ hK hKK hKA (by positivity) hv hKv
  have huKu : ω u (K u) = 0 :=
    apply_eq_zero_of_apply_eq_smul_add_smul hA₀ hK hKK hKA (by rw [neg_sq, neg_sq]; positivity)
      hu hKu
  obtain ⟨hli, hsymp⟩ := linearIndependent_and_isSymplectic_span_range_four hK hKK hvKv huKu hvu
  set f : Fin 4 → V := ![v, K v, u, K u]
  set U := Submodule.span ℝ (Set.range f)
  have hf (k : Fin 4) : f k ∈ U := Submodule.subset_span ⟨k, rfl⟩
  -- `U` is preserved by `K` and `A₀`, hence by the family.
  have hmaps {F : Module.End ℝ V} (hF : ∀ k, F (f k) ∈ U) : ∀ y ∈ U, F y ∈ U :=
    fun _ hy ↦ (Submodule.span_le (p := U.comap F)).2 (Set.range_subset_iff.2 hF) hy
  have hKU : ∀ y ∈ U, K y ∈ U := hmaps fun k ↦ by
    fin_cases k
    exacts [hf 1, by simpa [f, hKK] using neg_mem (hf 0), hf 3,
      by simpa [f, hKK] using neg_mem (hf 2)]
  have hA₀U : ∀ y ∈ U, A₀ y ∈ U := hmaps fun k ↦ by
    fin_cases k
    · simpa [f, hv] using add_mem (Submodule.smul_mem U a (hf 0)) (Submodule.smul_mem U b (hf 1))
    · simpa [f, hKv] using add_mem (Submodule.smul_mem U a (hf 1))
        (Submodule.smul_mem U b (hKU _ (hf 1)))
    · simpa [f, hu] using add_mem (Submodule.smul_mem U (-a) (hf 2))
        (Submodule.smul_mem U (-b) (hf 3))
    · simpa [f, hKu] using add_mem (Submodule.smul_mem U (-a) (hf 3))
        (Submodule.smul_mem U (-b) (hKU _ (hf 3)))
  have hinv (i : ι) : U ∈ Module.End.invtSubmodule (ω.hamiltonianEnd (Q i)) := by
    obtain ⟨p, q, hpq⟩ := hX i
    refine (Module.End.mem_invtSubmodule _).2 fun y hy ↦ ?_
    rw [Submodule.mem_comap, hpq]
    exact add_mem (Submodule.smul_mem U p (hA₀U y hy))
      (Submodule.smul_mem U q (hKU _ (hA₀U y hy)))
  have hfin : finrank ℝ V = 4 := by
    rcases hirr U hsymp hinv with hU | hU
    · have hv' := hf 0
      rw [hU, Submodule.mem_bot] at hv'
      exact absurd hv' hv0
    · rw [← finrank_top ℝ V, ← hU, finrank_span_eq_card hli, Fintype.card_fin]
  refine ⟨∅, {⟨a, b⟩}, by simp [hfin], by simp, by simp, by simp [ha, hb], fun z hz ↦ ?_⟩
  rw [Finset.mem_singleton.1 hz]
  refine ⟨v, -K v, hv0, by rw [hv]; simp, ?_⟩
  rw [map_neg, hKA, hv, map_add, map_smul, map_smul, hKK]
  module

/-- If a self-adjoint `J` with `J² = -1` commutes with an irreducible nondegenerate family with an
injective element `A`, then there is a self-adjoint `K` with `K² = -1` commuting with the family
such that every self-adjoint endomorphism commuting with the family lies in `ℝ + ℝ K`, and some
`A₀ ∈ {A, A + A J}` squares to `x₀ + y₁ K` with `y₁ > 0`. -/
private theorem exists_apply_apply_eq_smul_add_smul_of_mul_self_eq_neg_one
    (h : ω.IsNondegenerateQuadraticFamily Q) (hirr : IsIrreducible ω Q) [Nontrivial V]
    {A : Module.End ℝ V} (hA : IsSkewCentral ω Q A) (hAi : Function.Injective A)
    {J : Module.End ℝ V} (hJ : IsSymmCentral ω Q J) (hJJ : J * J = -1) :
    ∃ A₀ K : Module.End ℝ V, IsSkewCentral ω Q A₀ ∧ IsSymmCentral ω Q K ∧
      (∀ v, K (K v) = -v) ∧ (∀ E, IsSymmCentral ω Q E → ∃ a b : ℝ, E = algebraMap ℝ _ a + b • K) ∧
      ∃ x₀ y₁ : ℝ, 0 < y₁ ∧ ∀ v, A₀ (A₀ v) = x₀ • v + y₁ • K v := by
  have hspanJ (E : Module.End ℝ V) (hE : IsSymmCentral ω Q E) :
      ∃ a b : ℝ, E = algebraMap ℝ _ a + b • J := by
    rcases hE.eq_algebraMap_or_exists h hirr hA hAi with ⟨c, rfl⟩ | ⟨J', hJ', hJJ', a, b, rfl⟩
    · exact ⟨c, 0, by simp⟩
    · rcases eq_or_eq_neg_of_mul_self_eq_neg_one h hirr hA hAi hJ hJ' hJJ hJJ' with rfl | rfl
      · exact ⟨a, b, rfl⟩
      · exact ⟨a, -b, by simp⟩
  have hJpt (v : V) : J (J v) = -v := by simpa using LinearMap.congr_fun hJJ v
  have hJX {X : Module.End ℝ V} (hX : IsSkewCentral ω Q X) (v : V) : X (J v) = J (X v) :=
    LinearMap.congr_fun (hJ.commute h hX).symm.eq v
  -- Some `A₀` squares to `x₀ + y₀ J` with `y₀ ≠ 0`: `A` itself, or else `A + A J`.
  obtain ⟨A₀, hA₀, x₀, y₀, hy₀, hAA⟩ : ∃ A₀, IsSkewCentral ω Q A₀ ∧ ∃ x₀ y₀ : ℝ, y₀ ≠ 0 ∧
      ∀ v, A₀ (A₀ v) = x₀ • v + y₀ • J v := by
    obtain ⟨x, y, hxy⟩ := hspanJ _ (hA.mul h hA)
    have hAA (v : V) : A (A v) = x • v + y • J v := by
      simpa [Algebra.algebraMap_eq_smul_one] using LinearMap.congr_fun hxy v
    by_cases hy : y = 0
    · have hx : x ≠ 0 := by
        rintro rfl
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        exact hv (hAi (hAi (by simpa [hy] using hAA v)))
      refine ⟨A + A * J, hA.add (hA.mul_isSymmCentral h hJ), 0, 2 * x, by positivity,
        fun v ↦ ?_⟩
      simp only [LinearMap.add_apply, mul_apply_eq_comp, map_add, hJX hA, hAA, hy, zero_smul,
        add_zero, map_smul, map_neg, hJpt]
      module
    · exact ⟨A, hA, x, y, hy, hAA⟩
  -- Normalize the sign of `y₀` by replacing `J` with `-J`.
  rcases hy₀.lt_or_gt with hneg | hpos
  · refine ⟨A₀, -J, hA₀, by simpa using hJ.smul (-1), by simpa using hJpt, fun E hE ↦ ?_, x₀, -y₀,
      by linarith, fun v ↦ by simp [hAA]⟩
    obtain ⟨a, b, rfl⟩ := hspanJ E hE
    exact ⟨a, -b, by simp⟩
  · exact ⟨A₀, J, hA₀, hJ, hJpt, hspanJ, x₀, y₀, hpos, hAA⟩

/-- **The irreducible case with a complex structure.** If a self-adjoint `J` with `J² = -1`
commutes with an irreducible nondegenerate family with an injective element `A`, then every
self-adjoint endomorphism commuting with the family lies in `ℝ + ℝ J`, some `A₀ ∈ {A, A + A J}`
squares to `x₀ + y₀ J` with `y₀ ≠ 0`, and the span contains a regular focus-focus element. -/
private theorem exists_hasRegularSpectrum_of_mul_self_eq_neg_one
    (h : ω.IsNondegenerateQuadraticFamily Q) (hirr : IsIrreducible ω Q) [Nontrivial V]
    {A : Module.End ℝ V} (hA : IsSkewCentral ω Q A) (hAi : Function.Injective A)
    {J : Module.End ℝ V} (hJ : IsSymmCentral ω Q J) (hJJ : J * J = -1) :
    ∃ P₀ ∈ Submodule.span ℝ (Set.range Q), HasRegularSpectrum (ω.hamiltonianEnd P₀) := by
  obtain ⟨A₀, K, hA₀, hK, hKK, hspanK, x₀, y₁, hy₁, hAAK⟩ :=
    exists_apply_apply_eq_smul_add_smul_of_mul_self_eq_neg_one h hirr hA hAi hJ hJJ
  -- `a + b i` is the principal square root of `x₀ + y₁ i`, which lies in the open first quadrant.
  obtain ⟨a, b, ha, hb, hab, hab'⟩ :
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a ^ 2 - b ^ 2 = x₀ ∧ 2 * a * b = y₁ := by
    have hw := Complex.sq_sqrt ⟨x₀, y₁⟩
    refine ⟨_, _, (Complex.sqrt_re_pos_iff _).2 (Complex.mem_slitPlane_iff.2 (.inr hy₁.ne')),
      Complex.sqrt_im_pos hy₁, by simpa [sq] using congrArg Complex.re hw, ?_⟩
    have := congrArg Complex.im hw
    simp only [sq, Complex.mul_im] at this
    linarith
  obtain ⟨P₀, hP₀, rfl⟩ := h.exists_mem_span_hamiltonianEnd_eq hA₀.1 hA₀.2
  have hKA (v : V) : ω.hamiltonianEnd P₀ (K v) = K (ω.hamiltonianEnd P₀ v) :=
    LinearMap.congr_fun (hK.commute h hA₀).symm.eq v
  obtain ⟨v, u, hv0, hv, hu, hvu⟩ := exists_apply_eq_smul_add_smul_and_apply_eq_neg hA₀.1 hK.1
    hKK hKA ha fun v ↦ by rw [hab, hab', hAAK]
  exact ⟨P₀, hP₀, hasRegularSpectrum_of_apply_eq_smul_add_smul hirr hK.1 hKK hKA
    (fun i ↦ IsSkewCentral.exists_apply_eq_smul_add_smul h hA₀ hKK hspanK hy₁.ne' hAAK
      (isSkewCentral_hamiltonianEnd h (Submodule.subset_span ⟨i, rfl⟩))) ha hb hv0 hv hu hvu⟩

/-- **The irreducible case.** An irreducible nondegenerate family on a nonzero space has a regular
element in its span: either every self-adjoint endomorphism commuting with the family is a real
scalar and `V` is a plane, or one of them is a complex structure and `V` has dimension four. -/
private theorem exists_hasRegularSpectrum_of_isIrreducible (h : ω.IsNondegenerateQuadraticFamily Q)
    (hirr : IsIrreducible ω Q) [Nontrivial V] :
    ∃ P ∈ Submodule.span ℝ (Set.range Q), HasRegularSpectrum (ω.hamiltonianEnd P) := by
  obtain ⟨i, hi⟩ : ∃ i, ω.hamiltonianEnd (Q i) ≠ 0 := by
    by_contra! H
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (h.eq_zero_of_forall_hamiltonianEnd_apply_eq_zero fun i ↦ by simp [H i])
  have hP : Q i ∈ Submodule.span ℝ (Set.range Q) := Submodule.subset_span ⟨i, rfl⟩
  have hA := isSkewCentral_hamiltonianEnd h hP
  have hAi := (hA.eq_zero_or_injective h hirr).resolve_left hi
  by_cases hJ : ∃ J, IsSymmCentral ω Q J ∧ J * J = -1
  · obtain ⟨J, hJ, hJJ⟩ := hJ
    exact exists_hasRegularSpectrum_of_mul_self_eq_neg_one h hirr hA hAi hJ hJJ
  · refine ⟨Q i, hP, hasRegularSpectrum_of_forall_eq_algebraMap h hirr hP hAi fun E hE ↦ ?_⟩
    rcases hE.eq_algebraMap_or_exists h hirr hA hAi with hc | ⟨J, hJ', hJJ, -⟩
    · exact hc
    · exact absurd ⟨J, hJ', hJJ⟩ hJ

/-! ### Gluing along invariant symplectic splittings -/

/-- A positive scale `c` separating the spectral data of two summands: `c² s₂` avoids `s₁` and
`c t₂` avoids `t₁`. -/
private theorem exists_pos_forall_mul_notMem (s₁ s₂ : Finset ℝ) (t₁ t₂ : Finset ℂ)
    (hs₂ : (0 : ℝ) ∉ s₂) (ht₂ : ∀ z ∈ t₂, 0 < z.re ∧ 0 < z.im) :
    ∃ c : ℝ, 0 < c ∧ (∀ μ ∈ s₂, c ^ 2 * μ ∉ s₁) ∧ ∀ z ∈ t₂, (c : ℂ) * z ∉ t₁ := by
  obtain ⟨c, hc, hcB⟩ := (Set.Ioi_infinite (0 : ℝ)).exists_notMem_finset
    ((s₁ ×ˢ s₂).image (fun p ↦ √(p.1 / p.2)) ∪ (t₁ ×ˢ t₂).image (fun p ↦ (p.1 / p.2).re))
  have hc : 0 < c := hc
  refine ⟨c, hc, fun μ hμ hμ₁ ↦ hcB ?_, fun z hz hz₁ ↦ hcB ?_⟩
  · refine Finset.mem_union_left _ (Finset.mem_image.2
      ⟨(c ^ 2 * μ, μ), Finset.mem_product.2 ⟨hμ₁, hμ⟩, ?_⟩)
    have hμ0 : μ ≠ 0 := fun h0 ↦ hs₂ (h0 ▸ hμ)
    simp only [mul_div_assoc, div_self hμ0, mul_one]
    exact Real.sqrt_sq hc.le
  · refine Finset.mem_union_right _ (Finset.mem_image.2
      ⟨((c : ℂ) * z, z), Finset.mem_product.2 ⟨hz₁, hz⟩, ?_⟩)
    have hz0 : z ≠ 0 := fun h0 ↦ by simpa [h0] using (ht₂ z hz).1
    simp [mul_div_assoc, div_self hz0]

/-- **Combining regular spectra.** Let `V = L ⊕ L'` and let `A₁`, `A₂` have regular spectra on `L`
and `L'`. For some `c`, every endomorphism of `V` acting as `A₁` on `L` and as `c A₂` on `L'`
has regular spectrum: `c` separates the eigenvalues of `A₁` from those of `c A₂`. -/
private theorem exists_forall_hasRegularSpectrum {L L' : Submodule ℝ V} (hLL' : IsCompl L L')
    {A₁ : Module.End ℝ L} {A₂ : Module.End ℝ L'} (h₁ : HasRegularSpectrum A₁)
    (h₂ : HasRegularSpectrum A₂) :
    ∃ c : ℝ, ∀ A : Module.End ℝ V, (∀ a : L, A a = A₁ a) →
      (∀ b : L', A b = c • (A₂ b : V)) → HasRegularSpectrum A := by
  obtain ⟨s₁, t₁, hst₁, hs₁0, hs₁, ht₁0, ht₁⟩ := h₁
  obtain ⟨s₂, t₂, hst₂, hs₂0, hs₂, ht₂0, ht₂⟩ := h₂
  obtain ⟨c, hc, hcs, hct⟩ := exists_pos_forall_mul_notMem s₁ s₂ t₁ t₂ hs₂0 ht₂0
  refine ⟨c, fun A hA₁ hA₂ ↦ ?_⟩
  have hdisj₁ : Disjoint s₁ (s₂.image (c ^ 2 * ·)) := Finset.disjoint_left.2 fun μ hμ hμ' ↦ by
    obtain ⟨μ₂, hμ₂, rfl⟩ := Finset.mem_image.1 hμ'
    exact hcs μ₂ hμ₂ hμ
  have hdisj₂ : Disjoint t₁ (t₂.image ((c : ℂ) * ·)) := Finset.disjoint_left.2 fun z hz hz' ↦ by
    obtain ⟨z₂, hz₂, rfl⟩ := Finset.mem_image.1 hz'
    exact hct z₂ hz₂ hz
  refine ⟨s₁ ∪ s₂.image (c ^ 2 * ·), t₁ ∪ t₂.image ((c : ℂ) * ·), ?_, ?_, fun μ hμ ↦ ?_,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj₁, Finset.card_union_of_disjoint hdisj₂,
      Finset.card_image_of_injective _ (mul_right_injective₀ (by positivity)),
      Finset.card_image_of_injective _ (mul_right_injective₀ (by exact_mod_cast hc.ne')),
      ← Submodule.finrank_add_eq_of_isCompl hLL', ← hst₁, ← hst₂]
    ring
  · simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
    refine ⟨hs₁0, fun μ hμ h0 ↦ hs₂0 ?_⟩
    obtain rfl : μ = 0 :=
      (mul_eq_zero.1 (by linarith : c ^ 2 * μ = 0)).resolve_left (by positivity)
    exact hμ
  · rcases Finset.mem_union.1 hμ with hμ | hμ
    · obtain ⟨a, ha⟩ := (hs₁ μ hμ).exists_hasEigenvector
      have ha' : A₁ (A₁ a) = μ • a := by simpa [sq] using ha.apply_eq_smul
      refine hasEigenvalue_sq_of_apply (v := (a : V)) (by simpa using ha.2) ?_
      rw [hA₁, hA₁, ha', Submodule.coe_smul]
    · obtain ⟨μ₂, hμ₂, rfl⟩ := Finset.mem_image.1 hμ
      obtain ⟨b, hb⟩ := (hs₂ μ₂ hμ₂).exists_hasEigenvector
      have hb' : A₂ (A₂ b) = μ₂ • b := by simpa [sq] using hb.apply_eq_smul
      refine hasEigenvalue_sq_of_apply (v := (b : V)) (by simpa using hb.2) ?_
      rw [hA₂, map_smul, hA₂, hb']
      simp only [Submodule.coe_smul, smul_smul, sq, mul_assoc]
  · rcases Finset.mem_union.1 hz with hz | hz
    · exact ht₁0 z hz
    · obtain ⟨z₂, hz₂, rfl⟩ := Finset.mem_image.1 hz
      simpa [Complex.re_ofReal_mul, Complex.im_ofReal_mul, hc] using ht₂0 z₂ hz₂
  · rcases Finset.mem_union.1 hz with hz | hz
    · obtain ⟨v, w, hv, h₁, h₂⟩ := ht₁ z hz
      exact ⟨v, w, by simpa using hv, by rw [hA₁, h₁]; simp, by rw [hA₁, h₂]; simp⟩
    · obtain ⟨z₂, hz₂, rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨v, w, hv, h₁, h₂⟩ := ht₂ z₂ hz₂
      exact ⟨v, w, by simpa using hv, by rw [hA₂, h₁]; simp [smul_sub, smul_smul],
        by rw [hA₂, h₂]; simp [smul_add, smul_smul]⟩

/-- If `A_R` preserves a symplectic subspace `L` to which `R` restricts as `P`, then `A_R` acts on
`L` as the Hamiltonian endomorphism of `P` for the restricted symplectic form. -/
private theorem hamiltonianEnd_coe_of_comp_subtype_eq {L : Submodule ℝ V} (hL : ω.IsSymplectic L)
    {R : QuadraticForm ℝ V} (hRL : ∀ v ∈ L, ω.hamiltonianEnd R v ∈ L) {P : QuadraticForm ℝ L}
    (hRP : R.comp L.subtype = P) (a : L) :
    ω.hamiltonianEnd R a = ((ω.restrict L hL.nondegenerate_restrict).hamiltonianEnd P a : V) := by
  rw [← hRP, hamiltonianEnd_comp_subtype hL hRL, LinearMap.coe_restrict_apply]

/-- **Gluing regular elements.** Let a symplectic subspace `L` be preserved by a nondegenerate
family, and let `P₁` and `P₂` be regular elements of the restrictions of the family to `L` and to
`L^ω`. For a scale `c > 0` separating their spectra, the form equal to `P₁` on `L` and to `c P₂` on
`L^ω` is a regular element of the family. -/
private theorem exists_hasRegularSpectrum_of_isSymplectic (h : ω.IsNondegenerateQuadraticFamily Q)
    {L : Submodule ℝ V} (hL : ω.IsSymplectic L)
    (hQL : ∀ i, L ∈ Module.End.invtSubmodule (ω.hamiltonianEnd (Q i)))
    {P₁ : QuadraticForm ℝ L} (hP₁ : P₁ ∈ Submodule.span ℝ (Set.range fun i ↦ (Q i).comp L.subtype))
    (h₁ : HasRegularSpectrum ((ω.restrict L hL.nondegenerate_restrict).hamiltonianEnd P₁))
    {P₂ : QuadraticForm ℝ (ω.orthogonal L)}
    (hP₂ : P₂ ∈ Submodule.span ℝ (Set.range fun i ↦ (Q i).comp (ω.orthogonal L).subtype))
    (h₂ : HasRegularSpectrum
      ((ω.restrict (ω.orthogonal L) hL.orthogonal.nondegenerate_restrict).hamiltonianEnd P₂)) :
    ∃ P ∈ Submodule.span ℝ (Set.range Q), HasRegularSpectrum (ω.hamiltonianEnd P) := by
  obtain ⟨c, hcA⟩ := exists_forall_hasRegularSpectrum hL.isCompl h₁ h₂
  set R := (P₁.prod (c • P₂)).comp
    ((Submodule.prodEquivOfIsCompl L (ω.orthogonal L) hL.isCompl).symm :
      V →ₗ[ℝ] L × ω.orthogonal L)
  have hR : R ∈ Submodule.span ℝ (Set.range Q) := (h.mem_span_range_iff_exists_prod hL hQL).2
    ⟨P₁, hP₁, c • P₂, Submodule.smul_mem _ c hP₂, by
      ext x
      simp only [R, QuadraticMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]⟩
  -- `A_R` preserves `L` and `L^ω`, on which `R` restricts to `P₁` and `c P₂`.
  have hRL := ω.hamiltonianEnd_apply_mem_of_mem_span
    (fun i _ hv ↦ (Module.End.mem_invtSubmodule _).1 (hQL i) hv) hR
  have hRL' (x : V) (hx : x ∈ ω.orthogonal L) : ω.hamiltonianEnd R x ∈ ω.orthogonal L :=
    ((LinearMap.mem_skewAdjointSubmodule _).1
      (ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra R)).apply_mem_orthogonal hRL hx
  refine ⟨R, hR, hcA _ (hamiltonianEnd_coe_of_comp_subtype_eq hL hRL (P := P₁)
    (by ext a; simp [R])) fun b ↦ ?_⟩
  rw [hamiltonianEnd_coe_of_comp_subtype_eq hL.orthogonal hRL' (P := c • P₂) (by ext b; simp [R]),
    map_smul]
  simp

/-! ### Existence of regular elements -/

/-- Regular elements exist, by strong induction on the dimension: split off a proper invariant
symplectic subspace when there is one, and otherwise apply the irreducible case. -/
private theorem exists_hasRegularSpectrum_aux (n : ℕ) {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (σ : SymplecticForm W) {κ : Type*} (S : κ → QuadraticForm ℝ W)
    (hn : finrank ℝ W = n) (h : σ.IsNondegenerateQuadraticFamily S) :
    ∃ P ∈ Submodule.span ℝ (Set.range S), HasRegularSpectrum (σ.hamiltonianEnd P) := by
  induction n using Nat.strong_induction_on generalizing W with
  | _ n ih =>
  by_cases h0 : finrank ℝ W = 0
  · exact ⟨0, zero_mem _, ∅, ∅, by simp [h0], by simp, by simp, by simp, by simp⟩
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero h0)
  by_cases hirr : IsIrreducible σ S
  · exact exists_hasRegularSpectrum_of_isIrreducible h hirr
  simp only [IsIrreducible, not_forall, not_or] at hirr
  obtain ⟨L, hL, hSL, hL0, hLtop⟩ := hirr
  have hsum := Submodule.finrank_add_eq_of_isCompl hL.isCompl
  have hpos : 0 < finrank ℝ L := Nat.pos_of_ne_zero fun h0 ↦ hL0 (Submodule.finrank_eq_zero.1 h0)
  have hlt : finrank ℝ L < finrank ℝ W := Submodule.finrank_lt hLtop
  obtain ⟨P₁, hP₁, h₁⟩ := ih _ (hn ▸ hlt) _ _ rfl (h.restrict hL hSL)
  obtain ⟨P₂, hP₂, h₂⟩ := ih _ (by omega) _ _ rfl (h.restrict_orthogonal hL hSL)
  exact exists_hasRegularSpectrum_of_isSymplectic h hL hSL hP₁ h₁ hP₂ h₂

/-! ### Williamson's classification -/

/-- **Every nondegenerate family has a regular element.** The span of a nondegenerate family of
quadratic forms on `(V, ω)` contains a form `P` such that the square of its Hamiltonian
endomorphism has distinct nonzero real eigenvalues `μ ∈ s`, and the Hamiltonian endomorphism itself
has distinct eigenvalues `z = a + bi`, `a, b > 0`, `z ∈ t`, each with an eigenvector `v + iw`
(recorded as `v ≠ 0` and `w` with `A_P v = a v - b w`, `A_P w = b v + a w`), with
`2 |s| + 4 |t| = dim V`. -/
theorem exists_mem_span_card_mul_two_add_card_mul_four_eq_finrank
    (h : ω.IsNondegenerateQuadraticFamily Q) :
    ∃ P ∈ Submodule.span ℝ (Set.range Q), ∃ (s : Finset ℝ) (t : Finset ℂ),
      s.card * 2 + t.card * 4 = finrank ℝ V ∧ (0 : ℝ) ∉ s ∧
      (∀ μ ∈ s, (ω.hamiltonianEnd P ^ 2).HasEigenvalue μ) ∧ (∀ z ∈ t, 0 < z.re ∧ 0 < z.im) ∧
      ∀ z ∈ t, ∃ v w : V, v ≠ 0 ∧ ω.hamiltonianEnd P v = z.re • v - z.im • w ∧
        ω.hamiltonianEnd P w = z.im • v + z.re • w :=
  exists_hasRegularSpectrum_aux _ ω Q rfl h

/-- **Williamson's classification of nondegenerate families.** For every nondegenerate family `Q`
of quadratic forms on a finite-dimensional real symplectic vector space, that is, a family whose
Hamiltonian endomorphisms generate a Cartan subalgebra of `sp(V, ω)`, there are a Darboux basis
with `m + 2f` planes and a set of elliptic planes among the first `m` whose Williamson blocks span
the same space as `Q`: elliptic blocks `(xₖ² + yₖ²) / 2`, hyperbolic blocks `xₖ yₖ` and
focus-focus pairs `x y + x' y'`, `x y' - x' y` on disjoint symplectic coordinate planes. -/
theorem exists_isDarbouxBasis_span_eq_span_williamsonBlocks
    (h : ω.IsNondegenerateQuadraticFamily Q) :
    ∃ (m f : ℕ) (b : Basis (Fin (m + f * 2) × Fin 2) ℝ V) (u : Finset (Fin m)),
      ω.IsDarbouxBasis b ∧
        Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (williamsonBlocks b u)) :=
  h.exists_mem_span_card_mul_two_add_card_mul_four_eq_finrank_iff.1
    h.exists_mem_span_card_mul_two_add_card_mul_four_eq_finrank

end IsNondegenerateQuadraticFamily

end TauCeti.SymplecticForm
