/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import TauCeti.LinearAlgebra.LinearIndependent.BaseChange
import TauCeti.LinearAlgebra.Matrix.Idempotent.Basic
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous.Basic
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous.PositiveWeight

/-!
# Homogeneous bases of images of graded idempotents

Let `A` be a commutative `R`-algebra graded by `𝒜 : ℤ → Submodule R A`, concentrated in
nonnegative degrees, whose degree-zero part is a copy of `R`, a principal ideal domain. Give the
coordinate `j` of `ι → A` the shift `s j`, so that `v` is homogeneous of degree `d` when each
`v j` lies in `𝒜 (d - s j)`: this is the finite sum `⨁ⱼ A{s j}` with the convention
`(M{a})_d = M_(d - a)`. This file shows that the image of a degree-zero idempotent endomorphism
`p` of this sum is free with a finite basis of homogeneous vectors,
`TauCeti.exists_homogeneous_basis_range_idempotent`. In other words, every graded retract of a
finite sum of shifted copies of `A` is graded free.

The main example is a weighted polynomial ring over `ℤ` with positive weights,
`TauCeti.exists_weightedHomogeneous_basis_range_idempotent`, such as the ring
`Λ_N = ℤ[e₁, …, e_N]` of symmetric polynomials in `N` variables, with `eᵢ` in degree `2i`. This is
the coefficient ring of equivariant `gl(N)` foam evaluation, where homogeneous bases of such
images are what decompose a planar web into a finite sum of shifted empty webs.

The matrix of `p` has entries `p j k` of degree `s k - s j`, so it is block upper triangular for
the shifts, with diagonal blocks over `R`. Its block-diagonal part `p₀`, the reduction of `p`
modulo positive degrees, is an idempotent with entries in `R`. Over the principal ideal domain `R`,
the image of each block of `p₀` is free, and these bases give a basis of the image of `p₀` whose
vectors are homogeneous of the shift of their block. The difference `p - p₀` strictly raises the
shift, so `p` maps the image of `p₀` bijectively onto the image of `p`
(`Matrix.BlockTriangular.bijOn_range_blockDiagonalPart`). Since `p` has degree zero, it carries
the homogeneous basis of the image of `p₀` to a homogeneous basis of the image of `p`.

## Main results

* `TauCeti.exists_homogeneous_basis_range_idempotent`: the image of a degree-zero idempotent on a
  finite sum of shifts of a nonnegatively graded algebra with degree-zero part a principal ideal
  domain has a finite basis of homogeneous vectors.
* `TauCeti.exists_weightedHomogeneous_basis_range_idempotent`: the same for weighted polynomial
  rings over a principal ideal domain with positive integer weights.

## References

* L.-H. Robert and E. Wagner, *A closed formula for the evaluation of sl(N)-foams*,
  `arXiv:1702.04140v3`, Theorem 3.30, for the decomposition of planar webs that these bases
  provide.
* T. Y. Lam, *A First Course in Noncommutative Rings*, second edition, Graduate Texts in
  Mathematics 131, Springer (2001), §21, for idempotents that agree modulo a nil ideal.
-/

public section

open LinearMap Matrix

namespace TauCeti

section BlockDiagonal

/-! ### Block-diagonal idempotent matrices over a principal ideal domain -/

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → ℤ}

/-- The diagonal matrix projecting onto the coordinates of shift `t`. -/
private abbrev shiftMask (s : ι → ℤ) (t : ℤ) : Matrix ι ι R :=
  diagonal fun j ↦ if s j = t then 1 else 0

private theorem shiftMask_mulVec_apply (t : ℤ) (v : ι → R) (j : ι) :
    (shiftMask s t *ᵥ v) j = if s j = t then v j else 0 := by
  simp [shiftMask, mulVec_diagonal]

private theorem shiftMask_mul_self (t : ℤ) :
    shiftMask s t * shiftMask s t = (shiftMask s t : Matrix ι ι R) := by
  simp only [shiftMask, diagonal_mul_diagonal]
  congr 1
  ext j
  split_ifs <;> simp

variable {P : Matrix ι ι R} (hblock : ∀ j k, s j ≠ s k → P j k = 0)
include hblock

private theorem shiftMask_mul_comm (t : ℤ) : shiftMask s t * P = P * shiftMask s t := by
  ext j k
  rw [diagonal_mul, mul_diagonal]
  by_cases h : s j = s k
  · rw [h, mul_comm]
  · rw [hblock j k h, zero_mul, mul_zero]

private theorem isIdempotentElem_shiftMask_mul (hP : IsIdempotentElem P) (t : ℤ) :
    IsIdempotentElem (shiftMask s t * P) := by
  rw [IsIdempotentElem, mul_assoc, ← mul_assoc P, ← shiftMask_mul_comm hblock, mul_assoc,
    hP.eq, ← mul_assoc, shiftMask_mul_self]

private theorem mulVec_eq_self_of_mem_range_shiftMask_mul (hP : IsIdempotentElem P) {t : ℤ}
    {u : ι → R} (hu : u ∈ range (shiftMask s t * P).mulVecLin) : P *ᵥ u = u := by
  obtain ⟨w, rfl⟩ := hu
  rw [mulVecLin_apply, mulVec_mulVec, ← mul_assoc, ← shiftMask_mul_comm hblock, mul_assoc, hP.eq]

omit hblock in
private theorem apply_eq_zero_of_mem_range_shiftMask_mul {t : ℤ} {u : ι → R}
    (hu : u ∈ range (shiftMask s t * P).mulVecLin) {j : ι} (hj : s j ≠ t) : u j = 0 := by
  obtain ⟨w, rfl⟩ := hu
  rw [mulVecLin_apply, ← mulVec_mulVec, shiftMask_mulVec_apply]
  simp [hj]

private theorem shiftMask_mul_mulVec_of_mem (hP : IsIdempotentElem P) {t t' : ℤ} (htt' : t ≠ t')
    {u : ι → R} (hu : u ∈ range (shiftMask s t' * P).mulVecLin) :
    (shiftMask s t * P) *ᵥ u = 0 := by
  ext j
  rw [← mulVec_mulVec, mulVec_eq_self_of_mem_range_shiftMask_mul hblock hP hu,
    shiftMask_mulVec_apply]
  split_ifs with hj
  · exact apply_eq_zero_of_mem_range_shiftMask_mul hu (hj ▸ htt')
  · rfl

private theorem mulVec_single_mem_range_shiftMask_mul (k : ι) :
    P *ᵥ Pi.single k 1 ∈ range (shiftMask s (s k) * P).mulVecLin := by
  refine ⟨Pi.single k 1, funext fun j ↦ ?_⟩
  rw [mulVecLin_apply, ← mulVec_mulVec, shiftMask_mulVec_apply]
  split_ifs with hj
  · rfl
  · rw [mulVec_single_one, col_apply, hblock j k hj]

/-- Over a principal ideal domain, the image of each block of a block-diagonal idempotent matrix
`P` has a basis, and these bases have a dual family of linear forms: the coordinates of the
projection onto the image of each block. -/
private theorem exists_basis_dual_of_isIdempotentElem [IsDomain R] [IsPrincipalIdealRing R]
    (hP : IsIdempotentElem P) :
    ∃ (n : ℤ → ℕ)
      (b : ∀ t, Module.Basis (Fin (n t)) R (range (shiftMask (R := R) s t * P).mulVecLin))
      (φ : (Σ t : Set.range s, Fin (n t)) → Module.Dual R (ι → R)),
      ∀ x y, φ x (b y.fst y.snd) = if x = y then 1 else 0 := by
  classical
  have hb (t : ℤ) :
      ∃ n, Nonempty (Module.Basis (Fin n) R (range (shiftMask s t * P).mulVecLin)) :=
    ⟨_, ⟨(Submodule.basisOfPid (Pi.basisFun R ι) _).snd⟩⟩
  choose n hb using hb
  refine ⟨n, fun t ↦ (hb t).some, fun x ↦ ((hb x.fst).some.coord x.snd) ∘ₗ
    (shiftMask s x.fst * P).mulVecLin.rangeRestrict, fun x y ↦ ?_⟩
  obtain ⟨t, i⟩ := x
  obtain ⟨t', l⟩ := y
  by_cases htt : t = t'
  · subst htt
    have : (shiftMask s t * P).mulVecLin.rangeRestrict ((hb t).some l) = (hb t).some l :=
      Subtype.ext (((isIdempotentElem_shiftMask_mul hblock hP t).mulVecBilin R R).mem_range_iff.mp
        ((hb t).some l).property)
    simp only [LinearMap.comp_apply, this, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and, eq_comm]
  · have : (shiftMask s t * P).mulVecLin.rangeRestrict ((hb t').some l) = 0 :=
      Subtype.ext (shiftMask_mul_mulVec_of_mem hblock hP (Subtype.coe_injective.ne htt)
        ((hb t').some l).property)
    simp only [LinearMap.comp_apply, this, map_zero, Sigma.mk.inj_iff, htt, false_and, ite_false]

variable [IsDomain R] [IsPrincipalIdealRing R] {A : Type*} [CommRing A] (f : R →+* A)

omit [DecidableEq ι] in
/-- Let `P` be an idempotent matrix over a principal ideal domain `R` that is block diagonal for
the shifts `s`. After applying a ring homomorphism `f : R →+* A` entrywise, its image has a basis
consisting of the images under `f` of vectors over `R` supported in a single shift each. -/
private theorem exists_basis_range_map_of_isIdempotentElem (hP : IsIdempotentElem P) :
    ∃ (X : Type) (_ : Fintype X) (b : Module.Basis X A (range (P.map f).mulVecLin))
      (d : X → ℤ), ∀ x, ∃ u : ι → R, (b x : ι → A) = f ∘ u ∧ ∀ j, s j ≠ d x → u j = 0 := by
  classical
  obtain ⟨n, b, φ, hφ⟩ := exists_basis_dual_of_isIdempotentElem hblock hP
  -- Over `A`, the images `f ∘ b` stay independent, by the functionals applied after `f`.
  let v : (Σ t : Set.range s, Fin (n t)) → ι → A := fun x ↦ f ∘ (b x.fst x.snd : ι → R)
  have hli : LinearIndependent A v :=
    .map_of_pairwise_dual_eq_zero_one f _ φ (fun x y hxy ↦ by simp only [hφ, hxy, ite_false])
      fun x ↦ by simp only [hφ, ite_true]
  have hmem (x) : v x ∈ range (P.map f).mulVecLin :=
    ⟨v x, funext fun j ↦ by
      rw [mulVecLin_apply, ← RingHom.map_mulVec,
        mulVec_eq_self_of_mem_range_shiftMask_mul hblock hP (b x.fst x.snd).property]
      rfl⟩
  -- The images `f ∘ b` span: every column of `P` lies in the image of the block of its shift.
  have hspanU (t : Set.range s) (u : range (shiftMask s t * P).mulVecLin) :
      f ∘ (u : ι → R) ∈ Submodule.span A (Set.range v) := by
    have hu : f ∘ (u : ι → R) = ∑ i, f ((b t).repr u i) • v ⟨t, i⟩ := by
      ext j
      conv_lhs => rw [← (b t).sum_repr u]
      simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
        smul_eq_mul, map_sum, map_mul, v, Function.comp_apply]
    rw [hu]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hspan : range (P.map f).mulVecLin ≤ Submodule.span A (Set.range v) := by
    rintro _ ⟨w, rfl⟩
    rw [mulVecLin_apply, mulVec_eq_sum]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rw [op_smul_eq_smul]
    refine Submodule.smul_mem _ _ ?_
    have hk : (P.map f)ᵀ k = f ∘ (P *ᵥ Pi.single k 1) := by
      ext j
      simp
    rw [hk]
    exact hspanU ⟨s k, k, rfl⟩ ⟨_, mulVec_single_mem_range_shiftMask_mul hblock k⟩
  refine ⟨_, inferInstance, (Module.Basis.span hli).map (LinearEquiv.ofEq _ _
    (le_antisymm (Submodule.span_le.mpr (Set.range_subset_iff.mpr hmem)) hspan)), fun x ↦ x.fst,
    fun x ↦ ⟨b x.fst x.snd, ?_, fun j hj ↦ apply_eq_zero_of_mem_range_shiftMask_mul
      (b x.fst x.snd).property hj⟩⟩
  simp [v, Module.Basis.span_apply]

end BlockDiagonal

/-! ### Homogeneous bases -/

variable {R A : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing A]
  [Algebra R A] (𝒜 : ℤ → Submodule R A) [SetLike.GradedOne 𝒜]

omit [IsDomain R] [IsPrincipalIdealRing R] [SetLike.GradedOne 𝒜] in
/-- If a degree-zero endomorphism `p` maps a submodule `V` bijectively onto its image, then it
carries a homogeneous basis of `V` to a homogeneous basis of its image, reindexed by `Fin n`. -/
private theorem exists_homogeneous_basis_of_bijOn {ι X : Type*} [Finite X] {s : ι → ℤ}
    {p : Module.End A (ι → A)}
    (hhom : ∀ (d : ℤ) (v : ι → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j))
    {V : Submodule A (ι → A)} (hbij : Set.BijOn p V (range p)) (B : Module.Basis X A V)
    (dX : X → ℤ) (hB : ∀ x j, (B x : ι → A) j ∈ 𝒜 (dX x - s j)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A (range p)) (d : Fin n → ℤ),
      ∀ i j, (b i : ι → A) j ∈ 𝒜 (d i - s j) := by
  have := Fintype.ofFinite X
  let φ : V →ₗ[A] range p := (p.domRestrict V).codRestrict (range p) fun x ↦ mem_range_self p _
  have hφ : Function.Bijective φ := by
    refine ⟨fun x y hxy ↦ Subtype.ext (hbij.injOn x.property y.property
      (congrArg Subtype.val hxy)), fun y ↦ ?_⟩
    obtain ⟨x, hx, hxy⟩ := hbij.surjOn y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e := Fintype.equivFin X
  refine ⟨_, (B.map (LinearEquiv.ofBijective φ hφ)).reindex e, fun i ↦ dX (e.symm i),
    fun i j ↦ ?_⟩
  have hBi : ((B.map (LinearEquiv.ofBijective φ hφ)).reindex e i : ι → A) =
      p (B (e.symm i)) := by
    rw [Module.Basis.reindex_apply, Module.Basis.map_apply, LinearEquiv.ofBijective_apply]
    exact LinearMap.codRestrict_apply _ _ _
  rw [hBi]
  exact hhom _ _ (hB (e.symm i)) j

/-- Let `A` be graded by `𝒜` in nonnegative degrees, with degree-zero part a copy of the principal
ideal domain `R`, and give the coordinate `j` of `ι → A` the shift `s j`. Then the image of an
idempotent endomorphism `p` of degree zero has a finite basis of homogeneous vectors: the `i`th
basis vector has degree `d i`, that is, its coordinate `j` lies in `𝒜 (d i - s j)`. -/
theorem exists_homogeneous_basis_range_idempotent (h𝒜 : ∀ n < 0, 𝒜 n = ⊥)
    (h𝒜₀ : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra R A)) (hinj : Function.Injective (algebraMap R A))
    {ι : Type*} [Finite ι] (s : ι → ℤ) (p : Module.End A (ι → A)) (hp : IsIdempotentElem p)
    (hhom : ∀ (d : ℤ) (v : ι → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A (range p)) (d : Fin n → ℤ),
      ∀ i j, (b i : ι → A) j ∈ 𝒜 (d i - s j) := by
  classical
  have := Fintype.ofFinite ι
  set P := LinearMap.toMatrixAlgEquiv' p
  have hPP : IsIdempotentElem P := hp.map _
  -- The entry `P j k` is homogeneous of degree `s k - s j`, so `P` is block triangular.
  have hent (j k : ι) : P j k ∈ 𝒜 (s k - s j) := by
    refine hhom (s k) (Pi.single k 1) (fun j' ↦ ?_) j
    by_cases h : j' = k
    · subst h
      simpa using SetLike.GradedOne.one_mem
    · simp [h]
  have hBT : P.BlockTriangular s := fun j k hjk ↦ by
    have h := hent j k
    rwa [h𝒜 _ (by omega), Submodule.mem_bot] at h
  -- The block-diagonal part of `P`, its reduction modulo positive degrees, comes from `R`.
  have hlift (j k : ι) : ∃ r : R, s j = s k → algebraMap R A r = P j k := by
    by_cases h : s j = s k
    · obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (h𝒜₀ _ (by simpa [h] using hent j k))
      exact ⟨r, fun _ ↦ hr⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose Q₀ hQ₀ using hlift
  set Q := (Matrix.of Q₀).blockDiagonalPart s with hQdef
  have hQP : Q.map (algebraMap R A) = P.blockDiagonalPart s := by
    rw [hQdef, ← blockDiagonalPart_map _ _ (map_zero _)]
    ext j k
    by_cases h : s j = s k <;> simp [h, hQ₀ j k]
  have hblock (j k : ι) (h : s j ≠ s k) : Q j k = 0 := by simp [hQdef, h]
  have hQQ : IsIdempotentElem Q := by
    apply Matrix.map_injective hinj
    simpa only [Matrix.map_mul, hQP] using (hBT.isIdempotentElem_blockDiagonalPart hPP).eq
  -- `p` maps the image of the block-diagonal part bijectively onto its own image.
  have hbij := hBT.bijOn_range_blockDiagonalPart hPP
  have hp' : P.mulVecLin = p := LinearMap.ext fun v ↦ by
    rw [mulVecLin_apply, ← toLinAlgEquiv'_apply, toLinAlgEquiv'_toMatrixAlgEquiv']
  rw [hp', ← hQP] at hbij
  obtain ⟨X, _, B, dX, hB⟩ :=
    exists_basis_range_map_of_isIdempotentElem hblock (algebraMap R A) hQQ
  refine exists_homogeneous_basis_of_bijOn 𝒜 hhom hbij B dX fun x j ↦ ?_
  obtain ⟨u, hu, hsupp⟩ := hB x
  rw [hu, Function.comp_apply]
  by_cases hj : s j = dX x
  · rw [← hj, sub_self, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem
  · rw [hsupp j hj, map_zero]
    exact zero_mem _

/-- For a weighted polynomial ring over a principal ideal domain with positive integer weights,
the image of an idempotent endomorphism of degree zero of a finite sum of shifted copies has a
finite basis of weighted homogeneous vectors. For `R = ℤ`, `σ = Fin N` and weights `2 (i + 1)`,
this is the coefficient ring `Λ_N = ℤ[e₁, …, e_N]` with `eᵢ` in degree `2i`. -/
theorem exists_weightedHomogeneous_basis_range_idempotent {σ : Type*} (w : σ → ℤ)
    (hw : ∀ i, 0 < w i) {ι : Type*} [Finite ι] (s : ι → ℤ)
    (p : Module.End (MvPolynomial σ R) (ι → MvPolynomial σ R)) (hp : IsIdempotentElem p)
    (hhom : ∀ (d : ℤ) (v : ι → MvPolynomial σ R),
      (∀ j, v j ∈ MvPolynomial.weightedHomogeneousSubmodule R w (d - s j)) →
        ∀ j, p v j ∈ MvPolynomial.weightedHomogeneousSubmodule R w (d - s j)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (MvPolynomial σ R) (range p)) (d : Fin n → ℤ),
      ∀ i j, (b i : ι → MvPolynomial σ R) j ∈
        MvPolynomial.weightedHomogeneousSubmodule R w (d i - s j) :=
  have := (MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid (R := R) (w := w)).toGradedOne
  exists_homogeneous_basis_range_idempotent _
    (fun _ hn ↦ MvPolynomial.weightedHomogeneousSubmodule_eq_bot_of_neg (fun i ↦ (hw i).le) hn)
    (fun _ hx ↦ by
      rw [MvPolynomial.weightedHomogeneousSubmodule_zero_eq_range R hw] at hx
      exact Algebra.mem_bot.mpr (by simpa [Algebra.linearMap_apply] using hx))
    (MvPolynomial.C_injective σ R) s p hp hhom

end TauCeti
