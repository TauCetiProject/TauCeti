/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.LinearAlgebra.Charpoly.Dual
public import TauCeti.LinearAlgebra.Dimension.Submodule
public import TauCeti.LinearAlgebra.Eigenspace.Anticommute
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Neg

/-!
# Generalized eigenspaces of adjoint and skew-adjoint endomorphisms

Let `B` be a bilinear map on a module `M` over a commutative ring, and let `f`, `g` be an adjoint
pair of endomorphisms, `B (f x) y = B x (g y)` (`LinearMap.IsAdjointPair B B f g`). Then
`p(f)` and `p(g)` are adjoint for every polynomial `p`, so `B` pairs the kernel of `p(f)` to zero
against the range of `p(g)`. This file develops the consequences for generalized eigenspaces:

* `B` pairs the generalized `μ`-eigenspace of `f` to zero against the generalized `ν`-eigenspace
  of `g` whenever `μ - ν` is a unit (`LinearMap.IsAdjointPair.apply_eq_zero_of_mem_genEigenspace`),
  and more generally kills `ker p(f) × ker q(g)` for coprime polynomials `p`, `q`;
* when `B` is nondegenerate and `M` is Artinian, the kernel-range decomposition of a
  sufficiently high power of `g - μ` gives a nondegenerate pairing between the maximal
  generalized `μ`-eigenspaces of `f` and of `g`
  (`LinearMap.IsAdjointPair.nondegenerate_domRestrict₁₂_maxGenEigenspace`);
* over a field, for nondegenerate `B` on a finite-dimensional space, `B` conjugates `g` to the
  transpose of `f` (`LinearMap.IsAdjointPair.conj_toDual_flip`). Hence `ker g` and `ker f` have
  the same dimension, so do all generalized eigenspaces of `f` and `g`
  (`LinearMap.IsAdjointPair.finrank_genEigenspace_eq`), and `f` and `g` have the same
  characteristic polynomial (`LinearMap.IsAdjointPair.charpoly_eq`).

The main application is to a **skew-adjoint** endomorphism `f`, `B (f x) y = -B x (f y)`
(`LinearMap.IsSkewAdjoint`), such as an element of the symplectic Lie algebra `sp(V, ω)` or of an
orthogonal Lie algebra. Its adjoint is `-f`, whose generalized `ν`-eigenspace is the generalized
`-ν`-eigenspace of `f`, and `p(f)` has adjoint `p(-X)(f)`. Hence:

* the generalized `μ`- and `ν`-eigenspaces of `f` are `B`-orthogonal unless `μ + ν = 0`
  (when `μ + ν` is a unit; `LinearMap.IsSkewAdjoint.apply_eq_zero_of_mem_genEigenspace`), so for
  `2 μ` a unit the generalized `μ`-eigenspace is isotropic; likewise the vectors killed by powers
  of `p(f)` and of `q(f)` are `B`-orthogonal when `p` and `q(-X)` are coprime
  (`LinearMap.IsSkewAdjoint.apply_eq_zero_of_mem_maxGenEigenspace_aeval`);
* for nondegenerate `B`, the maximal generalized `μ`- and `-μ`-eigenspaces are paired
  nondegenerately (`LinearMap.IsSkewAdjoint.nondegenerate_domRestrict₁₂_maxGenEigenspace`);
* more generally, for any polynomial `p`, `B` pairs the vectors killed by a power of `p(f)`
  nondegenerately with those killed by a power of `p(-X)(f)`
  (`LinearMap.IsSkewAdjoint.nondegenerate_domRestrict₁₂_maxGenEigenspace_aeval`). For an even
  polynomial, `p(-X) = p`, the restriction of `B` to the vectors killed by a power of `p(f)` is
  therefore nondegenerate
  (`LinearMap.IsSkewAdjoint.nondegenerate_domRestrict₁₂_maxGenEigenspace_aeval_of_comp_neg_X_eq`).
  Over the reals this applies to `X² - a²`, `X² + b²` and
  `(X² - 2aX + a² + b²)(X² + 2aX + a² + b²)`, whose pieces are the hyperbolic, elliptic and
  focus-focus summands of Williamson's classification;
* over a field, `μ` and `-μ` have generalized eigenspaces of the same dimension for every
  exponent (`LinearMap.IsSkewAdjoint.finrank_genEigenspace_neg`), and on a space of dimension `n`
  the characteristic polynomial satisfies `χ_f(-X) = (-1)ⁿ χ_f(X)`
  (`LinearMap.IsSkewAdjoint.charpoly_comp_neg_X`): the eigenvalues of `f` come in pairs `±μ`
  with equal geometric and algebraic multiplicities.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Appendix 6.
-/

public section

open Module Polynomial

namespace LinearMap

variable {R M M₂ : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₂]
  [Module R M₂] {B : M →ₗ[R] M →ₗ[R] M₂} {f g : Module.End R M}

namespace IsAdjointPair

/-- Powers of an adjoint pair are adjoint. -/
theorem pow (h : IsAdjointPair B B f g) (n : ℕ) : IsAdjointPair B B ⇑(f ^ n) ⇑(g ^ n) := by
  induction n with
  | zero => simpa using isAdjointPair_one
  | succ n ih => rw [pow_succ, pow_succ']; exact ih.mul h

/-- Polynomials in an adjoint pair are adjoint. -/
theorem aeval (h : IsAdjointPair B B f g) (p : R[X]) :
    IsAdjointPair B B ⇑(aeval f p) ⇑(aeval g p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n a =>
    simpa [aeval_monomial, ← Algebra.smul_def] using (h.pow n).smul a

/-- An adjoint pair with the arguments of the form exchanged. -/
theorem flip (h : IsAdjointPair B B f g) : IsAdjointPair B.flip B.flip g f :=
  fun x y ↦ (h y x).symm

/-- Shifting an adjoint pair by the same scalar keeps it adjoint. -/
theorem sub_smul_one (h : IsAdjointPair B B f g) (μ : R) :
    IsAdjointPair B B ⇑(f - μ • 1) ⇑(g - μ • 1) :=
  h.sub (isAdjointPair_one.smul μ)

/-- `B` pairs the kernel of `p(f)` to zero against the kernel of `q(g)` when `p` and `q` are
coprime. -/
theorem apply_eq_zero_of_isCoprime (h : IsAdjointPair B B f g) {p q : R[X]}
    (hpq : IsCoprime p q) {v w : M} (hv : Polynomial.aeval f p v = 0)
    (hw : Polynomial.aeval g q w = 0) : B v w = 0 := by
  obtain ⟨a, b, hab⟩ := hpq
  have hw' : w = Polynomial.aeval g p (Polynomial.aeval g a w) := by
    rw [mul_comm a p] at hab
    simpa [mul_apply_eq_comp, hw] using congr(Polynomial.aeval g $hab w).symm
  rw [hw', ← h.aeval p, hv, LinearMap.map_zero₂]

/-- `B` pairs the generalized `μ`-eigenspace of `f` to zero against the generalized
`ν`-eigenspace of its adjoint `g` when `μ - ν` is a unit. -/
theorem apply_eq_zero_of_mem_genEigenspace (h : IsAdjointPair B B f g) {μ ν : R}
    (hμν : IsUnit (μ - ν)) {k l : ℕ∞} {v w : M} (hv : v ∈ f.genEigenspace μ k)
    (hw : w ∈ g.genEigenspace ν l) : B v w = 0 := by
  obtain ⟨a, -, hv⟩ := Module.End.mem_genEigenspace.1 hv
  obtain ⟨b, -, hw⟩ := Module.End.mem_genEigenspace.1 hw
  refine h.apply_eq_zero_of_isCoprime ((isCoprime_X_sub_C_of_isUnit_sub hμν).pow (m := a) (n := b))
    ?_ ?_
  · simpa [Algebra.algebraMap_eq_smul_one] using hv
  · simpa [Algebra.algebraMap_eq_smul_one] using hw

section Fitting

variable [IsArtinian R M]

/-- A vector of the maximal generalized `μ`-eigenspace of `f` which `B` pairs to zero with the
maximal generalized `μ`-eigenspace of the adjoint `g` is zero, when `B` is left-separating. -/
theorem eq_zero_of_mem_maxGenEigenspace (hB : B.SeparatingLeft) (h : IsAdjointPair B B f g)
    {μ : R} {v : M} (hv : v ∈ f.maxGenEigenspace μ)
    (hvw : ∀ w ∈ g.maxGenEigenspace μ, B v w = 0) : v = 0 := by
  -- The Artinian half of the Fitting argument gives ker (g - μ)ᵏ + range (g - μ)ᵏ = M.
  -- Choose k large enough that (f - μ)ᵏ v = 0 as well.
  obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace f μ v).1 hv
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (eventually_codisjoint_ker_pow_range_pow (g - μ • 1))
  have hn' : ((f - μ • 1) ^ (N + n)) v = 0 := by
    simp [pow_add, hn]
  refine hB v fun u ↦ ?_
  have hu : u ∈ ker ((g - μ • 1) ^ (N + n)) ⊔ range ((g - μ • 1) ^ (N + n)) := by
    rw [codisjoint_iff.1 (hN (N + n) (Nat.le_add_right N n))]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hu
  obtain ⟨c, rfl⟩ := mem_range.1 hb
  have ha' : a ∈ g.maxGenEigenspace μ :=
    (Module.End.mem_maxGenEigenspace g μ a).2 ⟨N + n, ha⟩
  rw [map_add, hvw a ha', ← (h.sub_smul_one μ).pow (N + n), hn', LinearMap.map_zero₂, zero_add]

/-- For a nondegenerate `B`, the maximal generalized `μ`-eigenspaces of an adjoint pair `f`, `g`
are paired nondegenerately by `B`. -/
theorem nondegenerate_domRestrict₁₂_maxGenEigenspace (hB : B.Nondegenerate)
    (h : IsAdjointPair B B f g) (μ : R) :
    (B.domRestrict₁₂ (f.maxGenEigenspace μ) (g.maxGenEigenspace μ)).Nondegenerate := by
  refine ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩
  · exact Subtype.ext <| h.eq_zero_of_mem_maxGenEigenspace hB.1 v.2 fun w hw ↦ hv ⟨w, hw⟩
  · exact Subtype.ext <| h.flip.eq_zero_of_mem_maxGenEigenspace (flip_separatingLeft.2 hB.2) w.2
      fun v hv ↦ hw ⟨v, hv⟩

end Fitting

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V} {f g : Module.End K V}

/-- For a nondegenerate bilinear form on a finite-dimensional space, `B` identifies the adjoint
`g` of `f` with the transpose of `f`: conjugating `g` by `y ↦ B (·) y` gives `f.dualMap`. -/
theorem conj_toDual_flip (hB : B.Nondegenerate) (h : IsAdjointPair B B f g) :
    (B.flip.toDual hB.flip).conj g = f.dualMap := by
  ext φ x
  obtain ⟨y, rfl⟩ := (B.flip.toDual hB.flip).surjective φ
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, dualMap_apply]
  exact (h x y).symm

/-- For a nondegenerate bilinear form on a finite-dimensional space, adjoint endomorphisms have
kernels of the same dimension: `B` identifies `g` with the transpose of `f`. -/
theorem finrank_ker_eq (hB : B.Nondegenerate) (h : IsAdjointPair B B f g) :
    finrank K (ker g) = finrank K (ker f) := by
  have hconj := ((B.flip.toDual hB.flip).finrank_ker_conj g).symm
  rw [h.conj_toDual_flip hB] at hconj
  exact hconj.trans f.finrank_ker_dualMap

/-- For a nondegenerate bilinear form on a finite-dimensional space, adjoint endomorphisms have
the same characteristic polynomial. -/
theorem charpoly_eq (hB : B.Nondegenerate) (h : IsAdjointPair B B f g) :
    g.charpoly = f.charpoly := by
  rw [← LinearEquiv.charpoly_conj (B.flip.toDual hB.flip), h.conj_toDual_flip hB,
    charpoly_dualMap]

/-- For a nondegenerate bilinear form on a finite-dimensional space, the generalized
`μ`-eigenspaces of adjoint endomorphisms have the same dimension, for every exponent. -/
theorem finrank_genEigenspace_eq (hB : B.Nondegenerate) (h : IsAdjointPair B B f g) (μ : K)
    (k : ℕ∞) :
    finrank K (g.genEigenspace μ k) = finrank K (f.genEigenspace μ k) := by
  have key : ∀ n : ℕ, finrank K (g.genEigenspace μ n) = finrank K (f.genEigenspace μ n) :=
    fun n ↦ by
      rw [Module.End.genEigenspace_nat, Module.End.genEigenspace_nat]
      exact ((h.sub_smul_one μ).pow n).finrank_ker_eq hB
  induction k using ENat.recTopCoe with
  | top =>
    -- The maximal-space lemmas use an abbreviation that rw does not unfold on their left side.
    -- Spell out exponent ⊤ so the equalities match the generalized eigenspaces in the goal.
    rw [show g.genEigenspace μ ⊤ = _ from g.maxGenEigenspace_eq_genEigenspace_finrank μ,
      show f.genEigenspace μ ⊤ = _ from f.maxGenEigenspace_eq_genEigenspace_finrank μ]
    exact key _
  | coe n => exact key n

end Field

end IsAdjointPair

namespace IsSkewAdjoint

/-- For a skew-adjoint `f`, the adjoint of `p(f)` is `p(-X)(f)`. -/
theorem isAdjointPair_aeval (h : B.IsSkewAdjoint f) (p : R[X]) :
    IsAdjointPair B B ⇑(Polynomial.aeval f p) ⇑(Polynomial.aeval f (p.comp (-X))) := by
  simpa [aeval_comp] using IsAdjointPair.aeval (f := f) (g := -f) h p

/-- For a skew-adjoint `f`, `B` pairs the generalized `μ`- and `ν`-eigenspaces of `f` to zero
when `μ + ν` is a unit. -/
theorem apply_eq_zero_of_mem_genEigenspace (h : B.IsSkewAdjoint f) {μ ν : R}
    (hμν : IsUnit (μ + ν)) {k l : ℕ∞} {v w : M} (hv : v ∈ f.genEigenspace μ k)
    (hw : w ∈ f.genEigenspace ν l) : B v w = 0 :=
  IsAdjointPair.apply_eq_zero_of_mem_genEigenspace (f := f) (g := -f) h (ν := -ν)
    (by simpa using hμν) hv (by simpa using hw)

/-- For a skew-adjoint `f`, `B` pairs the kernel of `p(f)` to zero against the kernel of `q(f)`
when `p` and `q(-X)` are coprime. -/
theorem apply_eq_zero_of_isCoprime (h : B.IsSkewAdjoint f) {p q : R[X]}
    (hpq : IsCoprime p (q.comp (-X))) {v w : M} (hv : Polynomial.aeval f p v = 0)
    (hw : Polynomial.aeval f q w = 0) : B v w = 0 :=
  IsAdjointPair.apply_eq_zero_of_isCoprime (f := f) (g := -f) h hpq hv
    (by simpa [aeval_comp] using hw)

/-- For a skew-adjoint `f`, `B` pairs the vectors killed by a power of `p(f)` to zero against those
killed by a power of `q(f)` when `p` and `q(-X)` are coprime. -/
theorem apply_eq_zero_of_mem_maxGenEigenspace_aeval (h : B.IsSkewAdjoint f) {p q : R[X]}
    (hpq : IsCoprime p (q.comp (-X))) {v w : M}
    (hv : v ∈ (Polynomial.aeval f p).maxGenEigenspace 0)
    (hw : w ∈ (Polynomial.aeval f q).maxGenEigenspace 0) : B v w = 0 := by
  obtain ⟨a, hv⟩ := (Module.End.mem_maxGenEigenspace _ _ v).1 hv
  obtain ⟨b, hw⟩ := (Module.End.mem_maxGenEigenspace _ _ w).1 hw
  refine h.apply_eq_zero_of_isCoprime (p := p ^ a) (q := q ^ b) ?_ ?_ ?_
  · simpa only [pow_comp] using hpq.pow
  · simpa using hv
  · simpa using hw

/-- For a skew-adjoint `f` and `2 μ` a unit, `B` vanishes on the generalized `μ`-eigenspace of
`f`. -/
theorem apply_eq_zero_of_mem_genEigenspace_self (h : B.IsSkewAdjoint f) {μ : R}
    (hμ : IsUnit (2 * μ)) {k l : ℕ∞} {v w : M} (hv : v ∈ f.genEigenspace μ k)
    (hw : w ∈ f.genEigenspace μ l) : B v w = 0 :=
  h.apply_eq_zero_of_mem_genEigenspace (by rwa [← two_mul]) hv hw

section Fitting

variable [IsArtinian R M]

/-- For a nondegenerate `B` and skew-adjoint `f`, the maximal generalized `μ`- and
`-μ`-eigenspaces of `f` are paired nondegenerately by `B`. -/
theorem nondegenerate_domRestrict₁₂_maxGenEigenspace (hB : B.Nondegenerate)
    (h : B.IsSkewAdjoint f) (μ : R) :
    (B.domRestrict₁₂ (f.maxGenEigenspace μ) (f.maxGenEigenspace (-μ))).Nondegenerate := by
  have hpair :=
    IsAdjointPair.nondegenerate_domRestrict₁₂_maxGenEigenspace (f := f) (g := -f) hB h μ
  -- The negation lemma uses an exponent; specialize to ⊤ under the maximal-space abbreviation
  -- so rw can match its left side without unfolding the subspaces.
  rwa [show (-f).maxGenEigenspace μ = f.maxGenEigenspace (-μ) from
    Module.End.genEigenspace_neg f μ ⊤] at hpair

/-- For a nondegenerate `B`, skew-adjoint `f` and any polynomial `p`, the vectors killed by a power
of `p(f)` are paired nondegenerately by `B` with those killed by a power of `p(-X)(f)`. -/
theorem nondegenerate_domRestrict₁₂_maxGenEigenspace_aeval (hB : B.Nondegenerate)
    (h : B.IsSkewAdjoint f) (p : R[X]) :
    (B.domRestrict₁₂ ((Polynomial.aeval f p).maxGenEigenspace 0)
      ((Polynomial.aeval f (p.comp (-X))).maxGenEigenspace 0)).Nondegenerate :=
  (h.isAdjointPair_aeval p).nondegenerate_domRestrict₁₂_maxGenEigenspace hB 0

/-- For a nondegenerate `B`, skew-adjoint `f` and an even polynomial `p`, `p(-X) = p`, the
restriction of `B` to the vectors killed by a power of `p(f)` is nondegenerate. -/
theorem nondegenerate_domRestrict₁₂_maxGenEigenspace_aeval_of_comp_neg_X_eq (hB : B.Nondegenerate)
    (h : B.IsSkewAdjoint f) {p : R[X]} (hp : p.comp (-X) = p) :
    (B.domRestrict₁₂ ((Polynomial.aeval f p).maxGenEigenspace 0)
      ((Polynomial.aeval f p).maxGenEigenspace 0)).Nondegenerate := by
  have := h.nondegenerate_domRestrict₁₂_maxGenEigenspace_aeval hB p
  rwa [hp] at this

end Fitting

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V} {f : Module.End K V}

/-- For a nondegenerate bilinear form on a finite-dimensional space and a skew-adjoint `f`, the
generalized `μ`- and `-μ`-eigenspaces of `f` have the same dimension, for every exponent. -/
theorem finrank_genEigenspace_neg (hB : B.Nondegenerate) (h : B.IsSkewAdjoint f) (μ : K)
    (k : ℕ∞) :
    finrank K (f.genEigenspace (-μ) k) = finrank K (f.genEigenspace μ k) := by
  rw [← Module.End.genEigenspace_neg]
  exact IsAdjointPair.finrank_genEigenspace_eq (f := f) (g := -f) hB h μ k

/-- For a nondegenerate bilinear form on a finite-dimensional space of dimension `n` and a
skew-adjoint `f`, the characteristic polynomial satisfies `χ_f(-X) = (-1)ⁿ χ_f(X)`: the
eigenvalues of `f` are symmetric under `μ ↦ -μ`, with multiplicities. -/
theorem charpoly_comp_neg_X (hB : B.Nondegenerate) (h : B.IsSkewAdjoint f) :
    f.charpoly.comp (-X) = (-1) ^ finrank K V * f.charpoly := by
  have hneg := charpoly_neg f
  rw [IsAdjointPair.charpoly_eq (f := f) (g := -f) hB h] at hneg
  conv_rhs => rw [hneg]
  simp [← mul_assoc, ← mul_pow]

/-- For a nondegenerate bilinear form on a finite-dimensional space and a skew-adjoint `f`, `-μ`
is a generalized eigenvalue of `f` exactly when `μ` is. -/
theorem hasUnifEigenvalue_neg_iff (hB : B.Nondegenerate) (h : B.IsSkewAdjoint f) {μ : K}
    {k : ℕ∞} : f.HasUnifEigenvalue (-μ) k ↔ f.HasUnifEigenvalue μ k := by
  simp only [Module.End.HasUnifEigenvalue, ne_eq, ← Submodule.finrank_eq_zero,
    h.finrank_genEigenspace_neg hB]

/-- For a nondegenerate bilinear form on a finite-dimensional space and a skew-adjoint `f`, `-μ`
is an eigenvalue of `f` exactly when `μ` is. -/
theorem hasEigenvalue_neg_iff (hB : B.Nondegenerate) (h : B.IsSkewAdjoint f) {μ : K} :
    f.HasEigenvalue (-μ) ↔ f.HasEigenvalue μ :=
  h.hasUnifEigenvalue_neg_iff hB

end Field

end IsSkewAdjoint

end LinearMap
