/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Generalized eigenspaces under a pairing with a multiplier

Let `B : M × M' → N` be a bilinear pairing and let `F`, `F'` be endomorphisms of `M` and `M'` which
multiply it by a scalar `c`: `B (F x) (F' y) = c • B x y`, written `B.compl₁₂ F F' = c • B`. The
example to keep in mind is Poincaré duality for a smooth proper variety over a finite field `𝔽_q`,
where `F` and `F'` are the geometric Frobenius on complementary cohomology groups and `c = q ^ d`
is the Frobenius eigenvalue on the target of the cup-product pairing. Another is a similitude of a
symmetric or alternating form, with `M = M'` and `F = F'`.

This file relates the generalized eigenspaces of `F` and `F'`. No semisimplicity is assumed, so
the dimensions below are algebraic, not geometric, multiplicities, and no splitting of the
characteristic polynomials is assumed either.

* The maximal generalized eigenspaces `M_α` of `F` and `M'_β` of `F'` are orthogonal unless
  `α * β = c` (`LinearMap.apply_eq_zero_of_mem_maxGenEigenspace`). This needs no finiteness, and
  holds over a domain for pairings with values in a torsion-free module.
* If `α * β = c` with `α` a unit, `B` is left-separating and `M'` is Artinian, then a vector of
  `M_α` orthogonal to `M'_β` is zero (`LinearMap.eq_zero_of_mem_maxGenEigenspace`). The proof moves
  `F - α` across the pairing, `B (F a) ((F' - β) b) = -β • B ((F - α) a) b`, and uses the
  kernel-range (Fitting) decomposition of a high power of `F' - β`.
* Over a field, if `B` is perfect and `c ≠ 0`, then `B` restricts to a perfect pairing of `M_α`
  with `M'_β` whenever `α * β = c` (`LinearMap.isPerfPair_domRestrict₁₂_maxGenEigenspace`), so these
  spaces have the same dimension (`LinearMap.finrank_maxGenEigenspace_eq_of_compl₁₂_eq_smul`).
  Consequently the eigenvalues of `F'` with algebraic multiplicity are the `c / α` for the
  eigenvalues `α` of `F` (`LinearMap.roots_charpoly_eq_map_div_of_compl₁₂_eq_smul`); over an
  algebraically closed field these are all the eigenvalues. For `M = M'` and `F = F'`, the
  eigenvalue multiset of `F` is stable under `α ↦ c / α`. A pairing of `F` with a different map
  does not give this: `F = 2` and `F' = 3` on `ℚ`, paired by multiplication, have `c = 6`, and the
  spectrum `{2}` of `F` is not stable under `α ↦ 6 / α`.
* If `B` identifies `M'` with the dual of a finite free module `M`, then
  `det F * det F' = c ^ finrank M` (`LinearMap.det_mul_det_eq_of_compl₁₂_eq_smul`).

The analogous statements for an adjoint pair, `B (f x) y = B x (g y)`, where the eigenvalues of `f`
and `g` match additively rather than multiplicatively, are in
`TauCeti.LinearAlgebra.SesquilinearForm.AdjointPair`.

## References

* P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), §2, (2.5)–(2.6).
* J. S. Milne, *Lectures on Étale Cohomology*, Remark 27.13 and Summary 27.14.
-/

public section

open Module Module.End Polynomial

namespace LinearMap

section CommRing

variable {R M M' N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [AddCommGroup N] [Module R N]

/-- The orthogonality of generalized eigenspaces, level by level: induction on the levels `m` and
`n`, using `F x = α • x + (F - α) x` and `F' y = β • y + (F' - β) y`. -/
private theorem apply_eq_zero_of_pow_sub_smul_apply_eq_zero [IsCancelMulZero R]
    [Module.IsTorsionFree R N] (B : M →ₗ[R] M' →ₗ[R] N) {F : End R M} {F' : End R M'}
    {c α β : R} (h : B.compl₁₂ F F' = c • B) (hαβ : α * β ≠ c) :
    ∀ (m n : ℕ) {x : M} {y : M'},
      ((F - α • 1) ^ m) x = 0 → ((F' - β • 1) ^ n) y = 0 → B x y = 0 := by
  intro m
  induction m with
  | zero => intro n x y hx _; simp [(by simpa using hx : x = 0)]
  | succ m ihm =>
    intro n
    induction n with
    | zero => intro x y _ hy; simp [(by simpa using hy : y = 0)]
    | succ n ihn =>
      intro x y hx hy
      have hx' : ((F - α • 1) ^ m) ((F - α • 1) x) = 0 := by
        rwa [← mul_apply_eq_comp, ← pow_succ]
      have hy' : ((F' - β • 1) ^ n) ((F' - β • 1) y) = 0 := by
        rwa [← mul_apply_eq_comp, ← pow_succ]
      have key : B (α • x + (F - α • 1) x) (β • y + (F' - β • 1) y) = c • B x y := by
        simpa using congr($h x y)
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, ihn hx hy',
        ihm (n + 1) hx' hy, ihm n hx' hy', smul_zero, add_zero] at key
      have hsub : (c - α * β) • B x y = 0 := by rw [sub_smul, mul_comm α β, mul_smul, key, sub_self]
      exact (smul_eq_zero_iff_right (sub_ne_zero.2 (Ne.symm hαβ))).1 hsub

/-- **Generalized eigenspaces are orthogonal unless their eigenvalues multiply to the
multiplier.** If `B (F x) (F' y) = c • B x y`, then the maximal generalized eigenspace of `F` at
`α` is orthogonal under `B` to that of `F'` at `β` unless `α * β = c`. -/
theorem apply_eq_zero_of_mem_maxGenEigenspace [IsCancelMulZero R] [Module.IsTorsionFree R N]
    (B : M →ₗ[R] M' →ₗ[R] N) {F : End R M} {F' : End R M'} {c α β : R}
    (h : B.compl₁₂ F F' = c • B) (hαβ : α * β ≠ c) {x : M} {y : M'}
    (hx : x ∈ F.maxGenEigenspace α) (hy : y ∈ F'.maxGenEigenspace β) : B x y = 0 := by
  obtain ⟨m, hm⟩ := (mem_maxGenEigenspace F α x).1 hx
  obtain ⟨n, hn⟩ := (mem_maxGenEigenspace F' β y).1 hy
  exact B.apply_eq_zero_of_pow_sub_smul_apply_eq_zero h hαβ m n hm hn

/-- **The two-space determinant identity.** If `B` identifies `M'` with the dual of the finite
free module `M` and `B (F x) (F' y) = c • B x y`, then `det F * det F' = c ^ finrank M`: under the
identification, `F'` is `c` times the inverse of the transpose of `F`. -/
theorem det_mul_det_eq_of_compl₁₂_eq_smul [Module.Free R M] [Module.Finite R M]
    (B : M →ₗ[R] M' →ₗ[R] R) (hB : Function.Bijective B.flip) {F : End R M} {F' : End R M'}
    {c : R} (h : B.compl₁₂ F F' = c • B) :
    LinearMap.det F * LinearMap.det F' = c ^ finrank R M := by
  let e : M' ≃ₗ[R] Dual R M := LinearEquiv.ofBijective B.flip hB
  have key : F.dualMap ∘ₗ ((e : M' →ₗ[R] Dual R M) ∘ₗ F' ∘ₗ (e.symm : Dual R M →ₗ[R] M')) =
      c • LinearMap.id := by
    ext φ x
    obtain ⟨y, rfl⟩ := e.surjective φ
    simpa [e] using congr($h x y)
  have hdet := congr(LinearMap.det $key)
  rw [det_comp, det_dualMap, det_conj, det_smul, det_id, mul_one] at hdet
  rw [hdet, (Free.chooseBasis R M).toDualEquiv.finrank_eq]

/-- Moving `F - α` across the pairing: if `α * β = c`, then
`B (F a) ((F' - β) b) = -β • B ((F - α) a) b`. -/
private theorem apply_apply_sub_smul (B : M →ₗ[R] M' →ₗ[R] N) {F : End R M} {F' : End R M'}
    {c α β : R} (h : B.compl₁₂ F F' = c • B) (hαβ : α * β = c) (a : M) (b : M') :
    B (F a) ((F' - β • 1) b) = -β • B ((F - α • 1) a) b := by
  have key : B (F a) (F' b) = c • B a b := by simpa using congr($h a b)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self, map_sub, map_smul,
    key, ← hαβ]
  module

/-- The `k`-th power of `apply_apply_sub_smul`: if `α * β = c`, then
`B (F ^ k u) ((F' - β) ^ k z) = (-β) ^ k • B ((F - α) ^ k u) z`. -/
private theorem apply_pow_apply_pow_sub_smul (B : M →ₗ[R] M' →ₗ[R] N) {F : End R M}
    {F' : End R M'} {c α β : R} (h : B.compl₁₂ F F' = c • B) (hαβ : α * β = c) (k : ℕ)
    (u : M) (z : M') :
    B ((F ^ k) u) (((F' - β • 1) ^ k) z) = (-β) ^ k • B (((F - α • 1) ^ k) u) z := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    have hcomm : (F - α • 1) * F ^ k = F ^ k * (F - α • 1) :=
      ((Commute.sub_left (Commute.refl F) (Commute.smul_left (Commute.one_left F) α))).pow_right k
    rw [pow_succ' F, pow_succ' (F' - β • 1), mul_apply_eq_comp, mul_apply_eq_comp,
      B.apply_apply_sub_smul h hαβ, ← mul_apply_eq_comp, hcomm, mul_apply_eq_comp, ih, smul_smul,
      ← pow_succ', ← mul_apply_eq_comp, ← pow_succ]

section Artinian

variable [IsArtinian R M']

/-- **A vector of a generalized eigenspace orthogonal to the paired generalized eigenspace
vanishes.** Let `B` be left-separating with `B (F x) (F' y) = c • B x y`, let `M'` be Artinian, and
let `α * β = c` with `α` a unit. A vector of the maximal generalized eigenspace of `F` at `α` which
`B` pairs to zero with the maximal generalized eigenspace of `F'` at `β` is zero. No splitting of
the characteristic polynomials is needed. -/
theorem eq_zero_of_mem_maxGenEigenspace (B : M →ₗ[R] M' →ₗ[R] N) (hB : B.SeparatingLeft)
    {F : End R M} {F' : End R M'} {c α β : R} (h : B.compl₁₂ F F' = c • B) (hα : IsUnit α)
    (hαβ : α * β = c) {x : M} (hx : x ∈ F.maxGenEigenspace α)
    (hxy : ∀ y ∈ F'.maxGenEigenspace β, B x y = 0) : x = 0 := by
  -- The Artinian half of the Fitting decomposition: `ker (F' - β) ^ k + range (F' - β) ^ k = M'`.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (eventually_codisjoint_ker_pow_range_pow (F' - β • 1))
  obtain ⟨n, hn⟩ := (mem_maxGenEigenspace F α x).1 hx
  -- Since `(X - α) ^ n` and `X ^ (N + n)` are coprime, `x = F ^ (N + n) u` with
  -- `(F - α) ^ n u = 0`.
  obtain ⟨a, b, hab⟩ : IsCoprime ((X - C α) ^ n) (X ^ (N + n)) := by
    simpa using (isCoprime_X_sub_C_of_isUnit_sub (a := α) (b := (0 : R)) (by simpa using hα)).pow
  have hP : aeval F ((X - C α) ^ n) = (F - α • 1) ^ n := by
    simp [Algebra.algebraMap_eq_smul_one]
  have hu : ((F - α • 1) ^ n) (aeval F b x) = 0 := by
    rw [← hP, ← mul_apply_eq_comp, ← map_mul, mul_comm, map_mul, mul_apply_eq_comp, hP, hn,
      map_zero]
  have hxu : x = (F ^ (N + n)) (aeval F b x) := by
    rw [mul_comm b] at hab
    have := congr(aeval F $hab x)
    rw [map_add, map_mul, map_mul, map_one, LinearMap.add_apply, mul_apply_eq_comp, hP, hn,
      map_zero, zero_add, mul_apply_eq_comp, map_pow, aeval_X, one_apply_eq_self] at this
    exact this.symm
  refine hB x fun w ↦ ?_
  have hw : w ∈ ker ((F' - β • 1) ^ (N + n)) ⊔ range ((F' - β • 1) ^ (N + n)) := by
    rw [codisjoint_iff.1 (hN (N + n) (Nat.le_add_right N n))]
    exact Submodule.mem_top
  obtain ⟨y, hy, _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add, hxy y ((mem_maxGenEigenspace F' β y).2 ⟨N + n, hy⟩), zero_add, hxu,
    B.apply_pow_apply_pow_sub_smul h hαβ, pow_add (F - α • 1) N n, mul_apply_eq_comp, hu, map_zero,
    map_zero, LinearMap.zero_apply, smul_zero]

end Artinian

end CommRing

section Field

variable {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
  (B : V →ₗ[K] V' →ₗ[K] K) [B.IsPerfPair] {F : End K V} {F' : End K V'} {c α β : K}

/-- **A perfect pairing with a multiplier restricts to perfect pairings of generalized
eigenspaces.** If `B` is perfect and `B (F x) (F' y) = c • B x y` with `c ≠ 0`, then for
`α * β = c` the pairing `B` restricts to a perfect pairing of the maximal generalized eigenspace of
`F` at `α` with that of `F'` at `β`. No splitting of the characteristic polynomials is needed. -/
theorem isPerfPair_domRestrict₁₂_maxGenEigenspace (h : B.compl₁₂ F F' = c • B) (hc : c ≠ 0)
    (hαβ : α * β = c) :
    (B.domRestrict₁₂ (F.maxGenEigenspace α) (F'.maxGenEigenspace β)).IsPerfPair := by
  have : IsReflexive K V := .of_isPerfPair B
  have : IsReflexive K V' := .of_isPerfPair B.flip
  have hB : B.IsPerfPair := inferInstance
  have hflip : B.flip.compl₁₂ F' F = c • B.flip := by
    ext y x
    simpa using congr($h x y)
  refine .of_injective ((injective_iff_map_eq_zero _).2 fun x hx ↦ ?_)
    ((injective_iff_map_eq_zero _).2 fun y hy ↦ ?_)
  · exact Subtype.ext <| B.eq_zero_of_mem_maxGenEigenspace hB.separatingLeft h
      (left_ne_zero_of_mul (hαβ ▸ hc)).isUnit hαβ x.property
      fun y hy ↦ by simpa [domRestrict₁₂_apply] using congr($hx ⟨y, hy⟩)
  · exact Subtype.ext <| B.flip.eq_zero_of_mem_maxGenEigenspace hB.separatingRight hflip
      (right_ne_zero_of_mul (hαβ ▸ hc)).isUnit ((mul_comm β α).trans hαβ) y.property
      fun x hx ↦ by simpa [domRestrict₁₂_apply] using congr($hy ⟨x, hx⟩)

/-- **Paired generalized eigenspaces have the same dimension.** If `B` is perfect and
`B (F x) (F' y) = c • B x y` with `c ≠ 0`, then the algebraic multiplicity of `β` as an eigenvalue
of `F'` is that of `α` as an eigenvalue of `F` whenever `α * β = c`. -/
theorem finrank_maxGenEigenspace_eq_of_compl₁₂_eq_smul (h : B.compl₁₂ F F' = c • B)
    (hc : c ≠ 0) (hαβ : α * β = c) :
    finrank K (F'.maxGenEigenspace β) = finrank K (F.maxGenEigenspace α) := by
  have : IsReflexive K V := .of_isPerfPair B
  have := B.isPerfPair_domRestrict₁₂_maxGenEigenspace h hc hαβ
  exact (finrank_of_isPerfPair
    (B.domRestrict₁₂ (F.maxGenEigenspace α) (F'.maxGenEigenspace β))).symm

/-- **Eigenvalues under a perfect pairing with a multiplier.** If `B` is perfect and
`B (F x) (F' y) = c • B x y` with `c ≠ 0`, then the eigenvalues of `F'` in `K`, counted with
algebraic multiplicity, are the `c / α` for the eigenvalues `α` of `F` in `K`. Over an
algebraically closed field these are all the eigenvalues. -/
theorem roots_charpoly_eq_map_div_of_compl₁₂_eq_smul [FiniteDimensional K V]
    [FiniteDimensional K V'] (h : B.compl₁₂ F F' = c • B) (hc : c ≠ 0) :
    F'.charpoly.roots = F.charpoly.roots.map (c / ·) := by
  classical
  have hinv : Function.Involutive (c / · : K → K) := fun γ ↦ div_div_cancel₀ hc
  ext β
  conv_rhs => rw [← hinv β, Multiset.count_map_eq_count' _ _ hinv.injective]
  simp only [count_roots]
  rcases eq_or_ne β 0 with rfl | hβ
  · -- Both maps are invertible, since `det F * det F' = c ^ finrank K V ≠ 0`.
    have hne : LinearMap.det F * LinearMap.det F' ≠ 0 :=
      B.det_mul_det_eq_of_compl₁₂_eq_smul (IsPerfPair.bijective_right B) h ▸ pow_ne_zero _ hc
    have hF : ¬F.HasEigenvalue 0 := ((not_hasEigenvalue_zero_tfae F).out 4 1).1
      (left_ne_zero_of_mul hne)
    have hF' : ¬F'.HasEigenvalue 0 := ((not_hasEigenvalue_zero_tfae F').out 4 1).1
      (right_ne_zero_of_mul hne)
    rw [div_zero, rootMultiplicity_eq_zero (mt (hasEigenvalue_iff_isRoot_charpoly F 0).2 hF),
      rootMultiplicity_eq_zero (mt (hasEigenvalue_iff_isRoot_charpoly F' 0).2 hF')]
  · rw [← finrank_maxGenEigenspace_eq, ← finrank_maxGenEigenspace_eq]
    exact B.finrank_maxGenEigenspace_eq_of_compl₁₂_eq_smul h hc (div_mul_cancel₀ c hβ)

end Field

end LinearMap
