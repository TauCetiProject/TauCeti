/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.Basic

/-!
# Semi-free resolutions of differential graded left modules

Every differential graded left module `N` over a differential graded algebra `A` has a
**semi-free resolution** (`TauCeti.IsDGLeftModule.exists_semiFreeResolution`): a row-finite
twisting cocycle `m` on a graded set of generators `(P, ind)` whose row relation
`y ∈ (m.m x).support` is well-founded, with a map `ε : K_m → N` of differential graded left
modules, given on the generators, whose relative cycles are relative boundaries. That is, `ε` is a
quasi-isomorphism from the semi-free module `K_m = P →₀ A` onto `N`, in the elementwise form used
by `TauCeti.RowFiniteTwistingCocycle.exists_lift_homotopy` and
`TauCeti.RowFiniteTwistingCocycle.exists_rowFiniteHomologous_homotopy`.

Those results show that semi-free row-finite modules are K-projective and that two semi-free
resolutions of the same module are homotopy equivalent, and
`TauCeti.RowFiniteTwistingCocycle.quasiIso_coefficientCochainComplexMap` shows that tensoring with a
semi-free module preserves quasi-isomorphisms. So for a resolution of `N` the twisted complexes
`M ⊗ ⟨P⟩` compute the derived tensor product `M ⊗^L_A N`, independently of the resolution, and
this file supplies a resolution for every `N`.

The resolution is built by attaching cells, as in Félix–Halperin–Thomas, Proposition 6.6. Start
from the zero module. At each stage, attach one free generator `e` for every homogeneous relative
cycle `(c, w)` of the current map `ε`, that is, every cycle `c` of the current free module with
`ε c = d w`, setting `D e = c` (`TauCeti.RowFiniteTwistingCocycle.attach`) and `ε e = w`. The
pair `(c, w)` is then the relative boundary `(D e, ε e)`. The generators of the resolution are those
of all the stages. Since a vector of the union has finite support, a relative cycle of the union
lives at some stage. Its homogeneous components were therefore killed at the next stage, and
`TauCeti.IsDGLeftModule.exists_of_forall_mem` assembles them. The row of a generator attached
at stage `k` only involves generators of earlier stages, which is why the row relation is
well-founded. No boundedness is assumed on the gradings of `A` or `N`, so the generator indices
need not be bounded below.

## Main results

* `TauCeti.IsDGLeftModule.exists_semiFreeResolution`: every differential graded left module has a
  semi-free resolution by a row-finite twisted module.

## References

* Y. Félix, S. Halperin, J.-C. Thomas, *Rational Homotopy Theory*, Graduate Texts in Mathematics
  205, Springer, 2001, Chapter 6, Proposition 6.6.
* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Section 3.
-/

public section

open Finsupp

namespace TauCeti

universe uR uA uN

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {N : Type uN} [AddCommGroup N] [Module R N] [Module A N]
  (𝒩 : ℤ → Submodule R N) (dN : N →ₗ[R] N)

namespace SemiFreeResolution

variable (𝒜 d) in
/-- A stage of the construction: a row-finite twisting cocycle with images of its generators. -/
private structure Stage where
  /-- The generators. -/
  P : Type (max uA uN)
  /-- The indices of the generators. -/
  ind : P → ℤ
  /-- The rows. -/
  m : RowFiniteTwistingCocycle 𝒜 d P ind
  /-- The images of the generators. -/
  ε : P → N

/-- The homogeneous relative cycles `(c, w)` of a stage, with `c` of total degree `n`, `w` of
degree `n - 1`, `D c = 0` and `ε c = dN w`. -/
@[reducible] private def Stage.Rel (S : Stage 𝒜 d (N := N)) : Type (max uA uN) :=
  {p : ℤ × (S.P →₀ A) × N // p.2.1 ∈ rowFiniteTotalGrading 𝒜 S.ind p.1 ∧ p.2.2 ∈ 𝒩 (p.1 - 1) ∧
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) S.m.m p.2.1 = 0 ∧
      linearCombination A S.ε p.2.1 = dN p.2.2}

/-- The next stage: one generator of index `1 - n` attached along each homogeneous relative cycle
`(c, w)` of degree `n`, with differential `c` and image `w`. -/
private noncomputable def Stage.step (S : Stage 𝒜 d (N := N)) : Stage 𝒜 d (N := N) where
  P := S.P ⊕ S.Rel 𝒩 dN
  ind := Sum.elim S.ind fun q ↦ 1 - q.1.1
  m := S.m.attach (indQ := fun q : S.Rel 𝒩 dN ↦ 1 - q.1.1) (fun q ↦ q.1.2.1)
    (fun q y ↦ by
      convert (mem_rowFiniteTotalGrading_iff 𝒜 S.ind).1 q.2.1 y using 2
      ring)
    fun q ↦ q.2.2.2.1
  ε := Sum.elim S.ε fun q ↦ q.1.2.2

variable (𝒜 d) in
/-- The stages, starting from the zero module. -/
private noncomputable def stage : ℕ → Stage 𝒜 d (N := N)
  | 0 => ⟨PEmpty, PEmpty.elim, 0, PEmpty.elim⟩
  | k + 1 => (stage k).step 𝒩 dN

variable (𝒜 d) in
/-- The generators of the resolution: the relative cycles killed at every stage. -/
private abbrev Gen : Type (max uA uN) :=
  Σ k, (stage 𝒜 d 𝒩 dN k).Rel 𝒩 dN

variable (𝒜 d) in
/-- The generators of a stage, among those of the resolution. -/
private noncomputable def emb : ∀ k, (stage 𝒜 d 𝒩 dN k).P → Gen 𝒜 d 𝒩 dN
  | 0 => PEmpty.elim
  | k + 1 => Sum.elim (emb k) fun q ↦ ⟨k, q⟩

variable (𝒜 d) in
/-- The index of a generator attached along a relative cycle of degree `n` is `1 - n`. -/
private def genInd (x : Gen 𝒜 d 𝒩 dN) : ℤ :=
  1 - x.2.1.1

variable (𝒜 d) in
/-- The row of a generator is its attaching cycle. -/
private noncomputable def genRow (x : Gen 𝒜 d 𝒩 dN) : Gen 𝒜 d 𝒩 dN →₀ A :=
  mapDomain (emb 𝒜 d 𝒩 dN x.1) x.2.1.2.1

variable (𝒜 d) in
/-- The image of a generator is the second component of its relative cycle. -/
private def genε (x : Gen 𝒜 d 𝒩 dN) : N :=
  x.2.1.2.2

private theorem fst_emb_lt : ∀ (k : ℕ) (x : (stage 𝒜 d 𝒩 dN k).P), (emb 𝒜 d 𝒩 dN k x).1 < k
  | 0, x => x.elim
  | k + 1, .inl x => (fst_emb_lt k x).trans (Nat.lt_succ_self k)
  | k + 1, .inr _ => Nat.lt_succ_self k

private theorem emb_injective : ∀ k, Function.Injective (emb 𝒜 d 𝒩 dN k)
  | 0 => fun x ↦ x.elim
  | k + 1 => by
    rintro (x | q) (x' | q') h
    · exact congrArg Sum.inl (emb_injective k h)
    · exact absurd (congrArg Sigma.fst h) (fst_emb_lt 𝒩 dN k x).ne
    · exact absurd (congrArg Sigma.fst h) (fst_emb_lt 𝒩 dN k x').ne'
    · exact congrArg Sum.inr (eq_of_heq (Sigma.mk.inj h).2)

private theorem mem_range_emb : ∀ (k : ℕ) (y : Gen 𝒜 d 𝒩 dN), y.1 < k →
    y ∈ Set.range (emb 𝒜 d 𝒩 dN k)
  | 0, _, hy => absurd hy (Nat.not_lt_zero _)
  | k + 1, ⟨j, q⟩, hy => by
    rcases (Nat.lt_succ_iff_lt_or_eq.1 hy) with hj | rfl
    · obtain ⟨x, hx⟩ := mem_range_emb k ⟨j, q⟩ hj
      exact ⟨.inl x, hx⟩
    · exact ⟨.inr q, rfl⟩

private theorem genInd_emb : ∀ (k : ℕ) (x : (stage 𝒜 d 𝒩 dN k).P),
    genInd 𝒜 d 𝒩 dN (emb 𝒜 d 𝒩 dN k x) = (stage 𝒜 d 𝒩 dN k).ind x
  | 0, x => x.elim
  | k + 1, .inl x => genInd_emb k x
  | _ + 1, .inr _ => rfl

private theorem genε_emb : ∀ (k : ℕ) (x : (stage 𝒜 d 𝒩 dN k).P),
    genε 𝒜 d 𝒩 dN (emb 𝒜 d 𝒩 dN k x) = (stage 𝒜 d 𝒩 dN k).ε x
  | 0, x => x.elim
  | k + 1, .inl x => genε_emb k x
  | _ + 1, .inr _ => rfl

/-- The rows of a stage are those of the resolution, relabelled. -/
private theorem genRow_emb : ∀ (k : ℕ) (x : (stage 𝒜 d 𝒩 dN k).P),
    genRow 𝒜 d 𝒩 dN (emb 𝒜 d 𝒩 dN k x) = mapDomain (emb 𝒜 d 𝒩 dN k) ((stage 𝒜 d 𝒩 dN k).m.m x)
  | 0, x => x.elim
  | k + 1, .inl x => (genRow_emb k x).trans <|
    (mapDomain_comp (f := Sum.inl) (g := emb 𝒜 d 𝒩 dN (k + 1))).trans <| congrArg _
      ((stage 𝒜 d 𝒩 dN k).m.attach_m_inl _ _ x).symm
  | k + 1, .inr q =>
    (mapDomain_comp (f := Sum.inl) (g := emb 𝒜 d 𝒩 dN (k + 1))).trans <| congrArg _
      ((stage 𝒜 d 𝒩 dN k).m.attach_m_inr
        (a := fun q : (stage 𝒜 d 𝒩 dN k).Rel 𝒩 dN ↦ q.1.2.1) _ _ q).symm

/-- The differential of the resolution restricts to that of each stage. -/
private theorem differential_mapDomain_emb (k : ℕ) (f : (stage 𝒜 d 𝒩 dN k).P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (genRow 𝒜 d 𝒩 dN)
        (mapDomain (emb 𝒜 d 𝒩 dN k) f) =
      mapDomain (emb 𝒜 d 𝒩 dN k) (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d)
        (stage 𝒜 d 𝒩 dN k).m.m f) :=
  rowFiniteTwistedDifferential_mapDomain _ _ (genRow_emb 𝒩 dN k) f

private theorem genRow_mem_rowFiniteTotalGrading (x : Gen 𝒜 d 𝒩 dN) :
    genRow 𝒜 d 𝒩 dN x ∈ rowFiniteTotalGrading 𝒜 (genInd 𝒜 d 𝒩 dN) x.2.1.1 := by
  classical
  refine (mem_rowFiniteTotalGrading_iff 𝒜 _).2 fun y ↦ ?_
  by_cases hy : y ∈ Set.range (emb 𝒜 d 𝒩 dN x.1)
  · obtain ⟨y, rfl⟩ := hy
    rw [genRow, mapDomain_apply_of_injective (emb_injective 𝒩 dN x.1), genInd_emb]
    exact (mem_rowFiniteTotalGrading_iff 𝒜 _).1 x.2.2.1 y
  · rw [genRow, mapDomain_of_notMem_range _ _ hy]
    exact zero_mem _

private theorem genRow_mem_graded (x y : Gen 𝒜 d 𝒩 dN) :
    genRow 𝒜 d 𝒩 dN x y ∈ 𝒜 (genInd 𝒜 d 𝒩 dN y - genInd 𝒜 d 𝒩 dN x + 1) := by
  convert (mem_rowFiniteTotalGrading_iff 𝒜 _).1 (genRow_mem_rowFiniteTotalGrading 𝒩 dN x) y
    using 2
  simp only [genInd]
  ring

variable (𝒜 d) in
/-- The row-finite twisting cocycle of the resolution. -/
private noncomputable def cocycle :
    RowFiniteTwistingCocycle 𝒜 d (Gen 𝒜 d 𝒩 dN) (genInd 𝒜 d 𝒩 dN) where
  m := genRow 𝒜 d 𝒩 dN
  mem_graded := genRow_mem_graded 𝒩 dN
  twisting x := (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero _
    (genRow_mem_graded 𝒩 dN x)).2 <| by
      rw [genRow, differential_mapDomain_emb, x.2.2.2.2.1, mapDomain_zero]

private theorem cocycle_m : (cocycle 𝒜 d 𝒩 dN).m = genRow 𝒜 d 𝒩 dN :=
  rfl

/-- The images of a stage are those of the resolution, through `emb`. -/
private theorem genε_comp_emb (k : ℕ) :
    genε 𝒜 d 𝒩 dN ∘ emb 𝒜 d 𝒩 dN k = (stage 𝒜 d 𝒩 dN k).ε :=
  funext (genε_emb 𝒩 dN k)

/-- A homogeneous relative cycle `(c, w)` of the resolution is the relative boundary of a single
generator: `c` lives at some stage `k`, where `(c, w)` was killed by a generator of stage
`k + 1`. -/
private theorem exists_differential_eq_of_mem (hA : IsDGAlgebra 𝒜 d) {n : ℤ}
    {c : Gen 𝒜 d 𝒩 dN →₀ A} {w : N} (hcn : c ∈ rowFiniteTotalGrading 𝒜 (genInd 𝒜 d 𝒩 dN) n)
    (hw : w ∈ 𝒩 (n - 1))
    (hc : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (cocycle 𝒜 d 𝒩 dN).m c = 0)
    (hcw : linearCombination A (genε 𝒜 d 𝒩 dN) c = dN w) :
    ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (cocycle 𝒜 d 𝒩 dN).m u = c ∧
      linearCombination A (genε 𝒜 d 𝒩 dN) u + dN v = w := by
  classical
  -- The finitely many generators of `c` all come from some stage `k`.
  obtain ⟨k, hk⟩ : ∃ k, ∀ y ∈ c.support, y.1 < k :=
    ⟨c.support.sup fun y ↦ y.1 + 1, fun y hy ↦
      Nat.lt_of_succ_le (Finset.le_sup (f := fun y : Gen 𝒜 d 𝒩 dN ↦ y.1 + 1) hy)⟩
  obtain ⟨c, rfl⟩ := (mem_range_mapDomain_iff _ (emb_injective 𝒩 dN k) _).2 fun y hy ↦
    notMem_support_iff.1 fun hy' ↦ hy (mem_range_emb 𝒩 dN k y (hk y hy'))
  -- So `(c, w)` is a homogeneous relative cycle of stage `k`, killed at stage `k + 1`.
  let q : (stage 𝒜 d 𝒩 dN k).Rel 𝒩 dN := ⟨(n, c, w), (mem_rowFiniteTotalGrading_iff 𝒜 _).2
    fun y ↦ by simpa [emb_injective 𝒩 dN k, genInd_emb] using
      (mem_rowFiniteTotalGrading_iff 𝒜 _).1 hcn (emb 𝒜 d 𝒩 dN k y),
    hw, mapDomain_injective (emb_injective 𝒩 dN k) <| by
      rw [← differential_mapDomain_emb, mapDomain_zero]
      exact hc,
    by rw [← genε_comp_emb, ← linearCombination_mapDomain]; exact hcw⟩
  refine ⟨single ⟨k, q⟩ 1, 0, ?_, ?_⟩
  · rw [(cocycle 𝒜 d 𝒩 dN).differential_single_one hA, cocycle_m, genRow]
  · rw [map_zero, add_zero, linearCombination_single, one_smul, genε]

end SemiFreeResolution

open SemiFreeResolution in
/-- **Every differential graded left module has a semi-free resolution.** For a differential graded
left module `N` over `A`, there are a row-finite twisting cocycle `m` on generators `(P, ind)`,
semi-free in that its row relation is well-founded, and images `ε x ∈ N` of degree `-ind x` of the
generators, such that `ε` commutes with the differentials and every relative cycle `(c, w)` of
`ε : K_m → N`, with `D c = 0` and `ε c = dN w`, is a relative boundary `(D u, ε u + dN v)`. So
`ε : K_m → N` is a quasi-isomorphism from a semi-free module. -/
theorem IsDGLeftModule.exists_semiFreeResolution [IsScalarTower R A N] {hA : IsDGAlgebra 𝒜 d}
    [SetLike.GradedSMul 𝒜 𝒩] [DirectSum.Decomposition 𝒩] (hN : IsDGLeftModule hA 𝒩 dN) :
    ∃ (P : Type (max uA uN)) (ind : P → ℤ) (m : RowFiniteTwistingCocycle 𝒜 d P ind) (ε : P → N),
      WellFounded (fun y x ↦ y ∈ (m.m x).support) ∧ (∀ x, ε x ∈ 𝒩 (-ind x)) ∧
      (∀ x, linearCombination A ε (m.m x) = dN (ε x)) ∧
      ∀ c w, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m c = 0 →
        linearCombination A ε c = dN w →
          ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m u = c ∧
            linearCombination A ε u + dN v = w := by
  have hε : ∀ x, genε 𝒜 d 𝒩 dN x ∈ 𝒩 (-genInd 𝒜 d 𝒩 dN x) := fun x ↦ by
    rw [genε, genInd, neg_sub]
    exact x.2.2.2.1
  refine ⟨Gen 𝒜 d 𝒩 dN, genInd 𝒜 d 𝒩 dN, cocycle 𝒜 d 𝒩 dN, genε 𝒜 d 𝒩 dN, ?_, hε, ?_, ?_⟩
  · -- A row only involves generators of earlier stages.
    refine Subrelation.wf (r := InvImage (· < ·) Sigma.fst) (fun {y x} hy ↦ ?_)
      (InvImage.wf _ wellFounded_lt)
    classical
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (mapDomain_support hy)
    exact fst_emb_lt 𝒩 dN x.1 y
  · intro x
    rw [cocycle_m, genRow, linearCombination_mapDomain, genε_comp_emb]
    exact x.2.2.2.2.2
  · -- By the homogeneous case, assembled over the homogeneous components.
    exact fun c w hc hcw ↦
      ((cocycle 𝒜 d 𝒩 dN).isDGLeftModule_rowFiniteTwistedDifferential hA).exists_of_forall_mem
        hN (isHomogeneous_linearCombination hε)
        (fun _ _ _ hcn hw ↦ exists_differential_eq_of_mem 𝒩 dN hA hcn hw) hc hcw

end TauCeti
