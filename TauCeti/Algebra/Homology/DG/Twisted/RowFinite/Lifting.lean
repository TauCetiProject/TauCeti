/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Basic
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Lifting maps out of row-finite twisted modules along quasi-isomorphisms

Let `m` be a row-finite twisting cocycle on a graded set of generators `(P, ind)` which is
one-sided, `m x y = 0` whenever `ind x ≤ ind y`, and whose generator indices are bounded below.
Its free differential graded left module `K_m = P →₀ A` is then built from zero by attaching
free generators along cycles, one index at a time, so it is a **semi-free** module, and maps out
of it can be built one generator at a time. This file proves that such modules are
**K-projective** and **cofibrant**:

* `TauCeti.RowFiniteTwistingCocycle.exists_lift_homotopy`: every degree-preserving chain map
  `g : K_m → N'` lifts, up to homotopy, along a quasi-isomorphism `φ : N → N'` of DG left
  modules. That is, there are a degree-preserving chain map `ĝ : K_m → N` and a homotopy `H` of
  degree `-1` with `g - φ ∘ ĝ = dN' ∘ H + H ∘ D`.
* `TauCeti.RowFiniteTwistingCocycle.exists_nullHomotopy`: every chain map from `K_m` to an
  acyclic DG left module is null-homotopic.
* `TauCeti.RowFiniteTwistingCocycle.exists_lift`: every chain map `K_m → N'` lifts strictly along
  a surjective quasi-isomorphism `N → N'`.

The quasi-isomorphism hypothesis is the elementwise statement that the mapping cone of `φ` is
acyclic: every relative cycle `(c, w)`, with `dN c = 0` and `φ c = dN' w`, is a relative
boundary `(dN u, φ u + dN' v)`. For right modules this is
`TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`.

A map out of the free module is given by the images of the generators, through
`Finsupp.linearCombination`, and a map of degree `-1` by the signed extension
`TauCeti.rowFiniteSignedMap` of the images of the generators, which carries the Koszul sign of
the coefficient. Both are determined by their values on generators: the chain map law and the
homotopy law hold on a vector as soon as they hold on the generators in its support
(`TauCeti.linearCombination_rowFiniteTwistedDifferential_of_forall_mem_support` and
`TauCeti.linearCombination_eq_add_rowFiniteSignedMap_of_forall_mem_support`).

The lift is built one index at a time. One-sidedness says that the row `m x` only involves
generators of strictly smaller index. If the lift and the homotopy are already constructed on
those, then the image of the row in `N` and the defect of `g x` form a relative cycle of `φ`;
a relative boundary for it supplies the values of the lift and the homotopy on `x`. Each step
only changes the generators of one index, so the stages stabilize on every generator, and the
bound below on the indices starts the induction.

These are the lifting properties by which the twisted complex of a semi-free resolution
computes a derived tensor product, independently of the chosen resolution.

## References

* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Section 3.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational Homotopy Theory*, GTM 205, Springer, 2001,
  Chapter 6 (semifree modules and the lifting lemma).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public section

open Finsupp

namespace TauCeti

universe uR uA uN uN' uP

variable {R : Type uR} {A : Type uA} {P : Type uP} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 d}
  {ind : P → ℤ}
  {N : Type uN} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  {𝒩 : ℤ → Submodule R N} [SetLike.GradedSMul 𝒜 𝒩] [DirectSum.Decomposition 𝒩]
  {dN : N →ₗ[R] N}
  {N' : Type uN'} [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
  {𝒩' : ℤ → Submodule R N'} [SetLike.GradedSMul 𝒜 𝒩'] [DirectSum.Decomposition 𝒩']
  {dN' : N' →ₗ[R] N'}

omit [Module R N] [IsScalarTower R A N] in
/-- The maps given on generators by `linearCombination` and `rowFiniteSignedMap` only depend on
the images of the generators in the support of the vector. -/
private theorem linearCombination_eq_and_rowFiniteSignedMap_eq {g g' : P → N} {k k' : P → N'}
    {f : P →₀ A} (h : ∀ y ∈ f.support, g y = g' y ∧ k y = k' y) :
    linearCombination A g f = linearCombination A g' f ∧
      rowFiniteSignedMap (𝒜 := 𝒜) k f = rowFiniteSignedMap (𝒜 := 𝒜) k' f := by
  refine ⟨?_, ?_⟩
  · simp only [linearCombination_apply]
    exact Finsupp.sum_congr fun y hy ↦ by rw [(h y hy).1]
  · exact rowFiniteSignedMap_congr fun y hy ↦ (h y hy).2

namespace RowFiniteTwistingCocycle

/-! ### Lifting along quasi-isomorphisms -/

section Lifting

variable (m : RowFiniteTwistingCocycle 𝒜 d P ind)

omit [GradedAlgebra 𝒜] in
/-- In a one-sided cocycle, the row of a generator only involves generators of smaller index. -/
private theorem lt_of_mem_support (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {x y : P}
    (hy : y ∈ (m.m x).support) : ind y < ind x :=
  lt_of_not_ge fun h ↦ mem_support_iff.mp hy (hm x y h)

variable (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0)
  (hN : IsDGLeftModule hA 𝒩 dN) (hN' : IsDGLeftModule hA 𝒩' dN')
  {φ : N →ₗ[A] N'} (hφ : LinearMap.IsHomogeneous φ 𝒩 𝒩' 0)
  (hφd : ∀ y, φ (dN y) = dN' (φ y))
  (hrel : ∀ c w, dN c = 0 → φ c = dN' w → ∃ u v, dN u = c ∧ φ u + dN' v = w)
  {g : P → N'} (hg : ∀ x, g x ∈ 𝒩' (-ind x))
  (hgd : ∀ x, linearCombination A g (m.m x) = dN' (g x))

/-- The chain map law of `ĝ` and the homotopy law of `k` on the generators of index below
`p`, with `ĝ` of degree zero and `k` of degree `-1`. -/
private def IsLiftBelow (g : P → N') (p : ℤ) (ĝ : P → N) (k : P → N') : Prop :=
  (∀ x, ĝ x ∈ 𝒩 (-ind x)) ∧ (∀ x, k x ∈ 𝒩' (-ind x - 1)) ∧
    ∀ x, ind x < p → linearCombination A ĝ (m.m x) = dN (ĝ x) ∧
      g x - φ (ĝ x) = dN' (k x) + rowFiniteSignedMap (𝒜 := 𝒜) k (m.m x)

include hm hN hN' hgd in
/-- On a generator `x`, the image of its row under `ĝ` and the defect `g x - H (m x)` form a
relative cycle of `φ`, as soon as the chain map law and the homotopy law hold on the generators of
smaller index, which are the ones involved in the row. -/
private theorem isRelativeCycle {ĝ : P → N} {k : P → N'} (x : P)
    (hlow : ∀ y, ind y < ind x → linearCombination A ĝ (m.m y) = dN (ĝ y) ∧
      g y - φ (ĝ y) = dN' (k y) + rowFiniteSignedMap (𝒜 := 𝒜) k (m.m y)) :
    dN (linearCombination A ĝ (m.m x)) = 0 ∧
      φ (linearCombination A ĝ (m.m x)) = dN' (g x - rowFiniteSignedMap (𝒜 := 𝒜) k (m.m x)) := by
  have hsupp (y : P) (hy : y ∈ (m.m x).support) := hlow y (lt_of_mem_support m hm hy)
  refine ⟨?_, ?_⟩
  · rw [← linearCombination_rowFiniteTwistedDifferential_of_forall_mem_support hN m.m
      fun y hy ↦ (hsupp y hy).1, m.differential_row x, map_zero]
  · have key := linearCombination_eq_add_rowFiniteSignedMap_of_forall_mem_support hN' m.m
      (e := fun y ↦ g y - φ (ĝ y)) fun y hy ↦ (hsupp y hy).2
    rw [m.differential_row x, map_zero, add_zero] at key
    simp only [linearCombination_apply, smul_sub, sum_sub] at key
    rw [map_sub, ← key, ← hgd x, linearCombination_apply, linearCombination_apply,
      map_finsuppSum]
    simp

include hm hN hN' hφ hrel hg hgd in
/-- **One step of the lift.** A lift and homotopy correct on the generators of index below `p`
can be changed on the generators of index `p`, and only there, to be correct on those too. -/
private theorem exists_isLiftBelow_add_one {p : ℤ} {ĝ : P → N} {k : P → N'}
    (h : IsLiftBelow m (φ := φ) (𝒩 := 𝒩) (dN := dN) (𝒩' := 𝒩') (dN' := dN') g p ĝ k) :
    ∃ (ĝ' : P → N) (k' : P → N'),
      IsLiftBelow m (φ := φ) (𝒩 := 𝒩) (dN := dN) (𝒩' := 𝒩') (dN' := dN') g (p + 1) ĝ' k' ∧
        ∀ x, ind x ≠ p → ĝ' x = ĝ x ∧ k' x = k x := by
  classical
  obtain ⟨hĝ, hk, hlow⟩ := h
  -- Choose homogeneous relative boundaries on the generators of index `p`.
  have hchoice (x : P) : ∃ (u : N) (v : N'), u ∈ 𝒩 (-ind x) ∧ v ∈ 𝒩' (-ind x - 1) ∧
      (ind x = p → dN u = linearCombination A ĝ (m.m x) ∧
        φ u + dN' v = g x - rowFiniteSignedMap (𝒜 := 𝒜) k (m.m x)) ∧
      (ind x ≠ p → u = ĝ x ∧ v = k x) := by
    by_cases hx : ind x = p
    · obtain ⟨hc₁, hc₂⟩ := isRelativeCycle m hm hN hN' hgd x fun y hy ↦ hlow y (hx ▸ hy)
      obtain ⟨u, v, hu, huv⟩ := hrel _ _ hc₁ hc₂
      have hc : linearCombination A ĝ (m.m x) ∈ 𝒩 (-ind x + 1) := by
        convert linearCombination_mem_of_mem_rowFiniteTotalGrading hĝ
          (m.m_mem_rowFiniteTotalGrading x) using 2
        ring
      have hw : g x - rowFiniteSignedMap (𝒜 := 𝒜) k (m.m x) ∈ 𝒩' (-ind x) := by
        refine sub_mem (hg x) ?_
        convert rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading (j := -1)
          (fun y ↦ by convert hk y using 2; ring) (m.m_mem_rowFiniteTotalGrading x) using 2
        ring
      refine ⟨DirectSum.decompose 𝒩 u (-ind x), DirectSum.decompose 𝒩' v (-ind x - 1),
        SetLike.coe_mem _, SetLike.coe_mem _, fun _ ↦ ⟨?_, ?_⟩, fun h ↦ (h hx).elim⟩
      · rw [hN.map_decompose, hu, DirectSum.decompose_of_mem_same _ hc]
      · rw [hφ.map_decompose, add_zero, hN'.map_decompose, sub_add_cancel, ← Submodule.coe_add,
          ← DirectSum.add_apply, ← DirectSum.decompose_add, huv,
          DirectSum.decompose_of_mem_same _ hw]
    · exact ⟨ĝ x, k x, hĝ x, hk x, fun h ↦ (hx h).elim, fun _ ↦ ⟨rfl, rfl⟩⟩
  choose ĝ' k' hĝ' hk' hp hoff using hchoice
  -- The new values agree with the old ones on the support of every row of index at most `p`.
  have hrow (x : P) (hx : ind x ≤ p) :=
    linearCombination_eq_and_rowFiniteSignedMap_eq (𝒜 := 𝒜) (f := m.m x) fun y hy ↦
      hoff y (lt_of_lt_of_le (lt_of_mem_support m hm hy) hx).ne
  refine ⟨ĝ', k', ⟨hĝ', hk', fun x hx ↦ ?_⟩, hoff⟩
  rw [(hrow x (Int.lt_add_one_iff.mp hx)).1, (hrow x (Int.lt_add_one_iff.mp hx)).2]
  rcases (Int.lt_add_one_iff.mp hx).lt_or_eq with hx | hx
  · rw [(hoff x hx.ne).1, (hoff x hx.ne).2]
    exact hlow x hx
  · refine ⟨((hp x hx).1).symm, ?_⟩
    have h2 := (hp x hx).2
    rw [eq_sub_iff_add_eq] at h2
    rw [sub_eq_iff_eq_add, ← h2]
    abel

include hm hN hN' hφ hrel hg hgd in
/-- **The stages of the lift.** There is a sequence of lifts and homotopies, the `n`th correct on
the generators of index below `p₀ + n`, each differing from the previous one only on the
generators of index `p₀ + n`. -/
private theorem exists_stages {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x) :
    ∃ stage : ℕ → (P → N) × (P → N'),
      (∀ n : ℕ, IsLiftBelow m (φ := φ) (𝒩 := 𝒩) (dN := dN) (𝒩' := 𝒩') (dN' := dN') g (p₀ + n)
        (stage n).1 (stage n).2) ∧
      ∀ (n : ℕ) x, ind x ≠ p₀ + n →
        (stage (n + 1)).1 x = (stage n).1 x ∧ (stage (n + 1)).2 x = (stage n).2 x := by
  let Stage (n : ℕ) := {D : (P → N) × (P → N') //
    IsLiftBelow m (φ := φ) (𝒩 := 𝒩) (dN := dN) (𝒩' := 𝒩') (dN' := dN') g (p₀ + n) D.1 D.2}
  have hstep (n : ℕ) (D : Stage n) : ∃ D' : Stage (n + 1),
      ∀ x, ind x ≠ p₀ + n → D'.1.1 x = D.1.1 x ∧ D'.1.2 x = D.1.2 x := by
    obtain ⟨ĝ', k', h', hoff⟩ := exists_isLiftBelow_add_one m hm hN hN' hφ hrel hg hgd D.2
    exact ⟨⟨(ĝ', k'), by rwa [Nat.cast_succ, ← add_assoc]⟩, hoff⟩
  -- Nothing is required below `p₀`, so the zero maps start the recursion.
  have h0 : Stage 0 := ⟨(0, 0), fun _ ↦ zero_mem _, fun _ ↦ zero_mem _, fun x hx ↦
    absurd (hp₀ x) (by simp only [Nat.cast_zero, add_zero] at hx; omega)⟩
  let stage : (n : ℕ) → Stage n := fun n ↦ Nat.rec h0 (fun n D ↦ (hstep n D).choose) n
  exact ⟨fun n ↦ (stage n).1, fun n ↦ (stage n).2, fun n ↦ (hstep n (stage n)).choose_spec⟩

include hm hN hN' hφ hrel hg hgd in
/-- **Semi-free modules are K-projective: lifting along quasi-isomorphisms up to homotopy.**
Let `m` be one-sided, with generator indices bounded below, and let `φ : N → N'` be a
degree-preserving `A`-linear map whose relative cycles are relative boundaries: every `(c, w)`
with `dN c = 0` and `φ c = dN' w` is `(dN u, φ u + dN' v)`. For a morphism of DG left modules this
says that `φ` is a quasi-isomorphism. Then every degree-preserving chain map `g : K_m → N'`,
given by the images of the generators, lifts up to homotopy along `φ`: there are a
degree-preserving chain map `ĝ : K_m → N` and a homotopy `H` of degree `-1`, the signed extension
of `k`, with `g - φ ∘ ĝ = dN' ∘ H + H ∘ D`. -/
theorem exists_lift_homotopy {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x) :
    ∃ (ĝ : P → N) (k : P → N'), (∀ x, ĝ x ∈ 𝒩 (-ind x)) ∧ (∀ x, k x ∈ 𝒩' (-ind x - 1)) ∧
      (∀ f, linearCombination A ĝ (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) =
        dN (linearCombination A ĝ f)) ∧
      ∀ f, linearCombination A g f - φ (linearCombination A ĝ f) =
        dN' (rowFiniteSignedMap (𝒜 := 𝒜) k f) +
          rowFiniteSignedMap (𝒜 := 𝒜) k (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) := by
  classical
  obtain ⟨stage, hgood, hstage⟩ := exists_stages m hm hN hN' hφ hrel hg hgd hp₀
  -- Once a generator is below the stage, its values no longer change.
  have hstable (x : P) (n : ℕ) (hx : ind x < p₀ + n) (j : ℕ) :
      (stage (n + j)).1 x = (stage n).1 x ∧ (stage (n + j)).2 x = (stage n).2 x := by
    induction j with
    | zero => exact ⟨rfl, rfl⟩
    | succ j ih =>
      rw [← add_assoc, (hstage (n + j) x (by push_cast; omega)).1,
        (hstage (n + j) x (by push_cast; omega)).2]
      exact ih
  -- The limit takes the value of the first stage above each generator.
  let s (x : P) : ℕ := (ind x - p₀ + 1).toNat
  have hs (x : P) : ind x < p₀ + s x := by
    have := hp₀ x
    simp only [s]
    omega
  refine ⟨fun x ↦ (stage (s x)).1 x, fun x ↦ (stage (s x)).2 x,
    fun x ↦ (hgood (s x)).1 x, fun x ↦ (hgood (s x)).2.1 x, ?_⟩
  -- On the support of the row of `x`, the limit agrees with the stage of `x`.
  have hrow (x : P) :
      linearCombination A (fun y ↦ (stage (s y)).1 y) (m.m x) =
          linearCombination A (stage (s x)).1 (m.m x) ∧
        rowFiniteSignedMap (𝒜 := 𝒜) (fun y ↦ (stage (s y)).2 y) (m.m x) =
          rowFiniteSignedMap (𝒜 := 𝒜) (stage (s x)).2 (m.m x) := by
    refine linearCombination_eq_and_rowFiniteSignedMap_eq fun y hy ↦ ?_
    have hle : s y ≤ s x := by
      have := lt_of_mem_support m hm hy
      simp only [s]
      omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
    rw [hj, (hstable y (s y) (hs y) j).1, (hstable y (s y) (hs y) j).2]
    exact ⟨rfl, rfl⟩
  have hlaw (x : P) := (hgood (s x)).2.2 x (hs x)
  refine ⟨linearCombination_rowFiniteTwistedDifferential hN m.m fun x ↦ ?_, fun f ↦ ?_⟩
  · rw [(hrow x).1]
    exact (hlaw x).1
  · have key := linearCombination_eq_add_rowFiniteSignedMap hN' m.m
      (e := fun y ↦ g y - φ ((stage (s y)).1 y)) (fun x ↦ by rw [(hrow x).2]; exact (hlaw x).2) f
    rw [← key]
    simp [linearCombination_apply, smul_sub, sum_sub, map_finsuppSum]

include hm hN in
/-- **Semi-free modules are K-projective: maps into acyclic modules are null-homotopic.** Let
`m` be one-sided, with generator indices bounded below, and let `N` be an acyclic DG left
module: every cycle is a boundary. Then every degree-preserving chain map `g : K_m → N` is
null-homotopic: `g = dN ∘ H + H ∘ D` for the signed extension `H` of some `k` of degree `-1`. -/
theorem exists_nullHomotopy {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x)
    (hacyc : ∀ c, dN c = 0 → ∃ u, dN u = c) {g : P → N} (hg : ∀ x, g x ∈ 𝒩 (-ind x))
    (hgd : ∀ x, linearCombination A g (m.m x) = dN (g x)) :
    ∃ k : P → N, (∀ x, k x ∈ 𝒩 (-ind x - 1)) ∧
      ∀ f, linearCombination A g f = dN (rowFiniteSignedMap (𝒜 := 𝒜) k f) +
        rowFiniteSignedMap (𝒜 := 𝒜) k (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) := by
  obtain ⟨_, k, _, hk, _, hgk⟩ := exists_lift_homotopy m hm hN hN
    (LinearMap.isHomogeneous_zero 𝒩 𝒩 0) (φ := 0)
    (fun c w hc hw ↦ by
      obtain ⟨u, hu⟩ := hacyc c hc
      obtain ⟨v, hv⟩ := hacyc w (by simpa using hw.symm)
      exact ⟨u, v, hu, by simpa using hv⟩) hg hgd hp₀
  exact ⟨k, hk, fun f ↦ by simpa using hgk f⟩

include hm hN hN' hφ hφd hrel hg hgd in
/-- **Semi-free modules are cofibrant: strict lifting along surjective quasi-isomorphisms.** Let
`m` be one-sided, with generator indices bounded below, and let `φ : N → N'` be a surjective
degree-preserving quasi-isomorphism of DG left modules. Then every degree-preserving chain map
`g : K_m → N'` factors through `φ` as a degree-preserving chain map `ĝ : K_m → N`. -/
theorem exists_lift {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x) (hφs : Function.Surjective φ) :
    ∃ ĝ : P → N, (∀ x, ĝ x ∈ 𝒩 (-ind x)) ∧
      (∀ f, linearCombination A ĝ (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) =
        dN (linearCombination A ĝ f)) ∧
      ∀ f, φ (linearCombination A ĝ f) = linearCombination A g f := by
  classical
  obtain ⟨ĝ, k, hĝ, hk, hĝd, hgk⟩ := exists_lift_homotopy m hm hN hN' hφ hrel hg hgd hp₀
  -- Lift the homotopy to `N`, in the same degrees.
  have hlift (x : P) : ∃ l : N, l ∈ 𝒩 (-ind x - 1) ∧ φ l = k x := by
    obtain ⟨l, hl⟩ := hφs (k x)
    refine ⟨DirectSum.decompose 𝒩 l (-ind x - 1), SetLike.coe_mem _, ?_⟩
    rw [hφ.map_decompose, add_zero, hl, DirectSum.decompose_of_mem_same _ (hk x)]
  choose l hl hφl using hlift
  have hφk : φ ∘ l = k := funext hφl
  -- Correct the lift by the null-homotopic map `dN ∘ L + L ∘ D`, where `L` lifts the homotopy.
  let e (x : P) : N := dN (l x) + rowFiniteSignedMap (𝒜 := 𝒜) l (m.m x)
  have he (f : P →₀ A) : linearCombination A e f = dN (rowFiniteSignedMap (𝒜 := 𝒜) l f) +
      rowFiniteSignedMap (𝒜 := 𝒜) l (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) :=
    linearCombination_eq_add_rowFiniteSignedMap hN m.m (fun _ ↦ rfl) f
  have hsum (f : P →₀ A) :
      linearCombination A (ĝ + e) f = linearCombination A ĝ f + linearCombination A e f := by
    simp [linearCombination_apply, smul_add, sum_add]
  have hφS (f : P →₀ A) :
      φ (rowFiniteSignedMap (𝒜 := 𝒜) l f) = rowFiniteSignedMap (𝒜 := 𝒜) k f := by
    rw [LinearMap.map_rowFiniteSignedMap, hφk]
  refine ⟨ĝ + e, fun x ↦ add_mem (hĝ x) (add_mem ?_ ?_), fun f ↦ ?_, fun f ↦ ?_⟩
  · convert hN.isHomogeneous.map_mem (hl x) using 2
    ring
  · convert rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading (j := -1)
      (fun y ↦ by convert hl y using 2; ring) (m.m_mem_rowFiniteTotalGrading x) using 2
    ring
  · rw [hsum, hsum, hĝd, he, he, m.differential_sq_zero hA, map_zero, add_zero]
    simp only [map_add, hN.sq_zero, zero_add]
  · rw [hsum, map_add, he, map_add, hφd, hφS, hφS, ← hgk f]
    abel

end Lifting

end RowFiniteTwistingCocycle

end TauCeti
